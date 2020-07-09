use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::plonk::circuit::bigint::field::*;
use franklin_crypto::plonk::circuit::verifier_circuit::*;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::*;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::aux_data::*;
use franklin_crypto::plonk::circuit::verifier_circuit::data_structs::*;
use franklin_crypto::plonk::circuit::verifier_circuit::verifying_circuit::aggregate_proof;
use franklin_crypto::plonk::circuit::verifier_circuit::channel::*;
use franklin_crypto::rescue::*;
use franklin_crypto::circuit::Assignment;

use franklin_crypto::bellman::SynthesisError;

use franklin_crypto::bellman::plonk::better_cs::generator::make_non_residues;
use franklin_crypto::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;

#[derive(Clone, Debug)]
pub struct RecursiveAggregationCircuit<
    'a, 
    E: RescueEngine, 
    P: OldCSParams<E>, 
    WP: WrappedAffinePoint<'a, E>, 
    AD: AuxData<E>,
    T: ChannelGadget<E>,
> {
    pub num_proofs_to_check: usize,
    pub num_inputs: usize,
    pub vk_tree_depth: usize,
    pub vk_root: Option<E::Fr>,
    pub vk_witnesses: Option<Vec<VerificationKey<E, P>>>,
    pub proof_ids: Option<Vec<usize>>,
    pub proofs: Option<Vec<Proof<E, P>>>,
    pub rescue_params: &'a E::Params,
    pub rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    pub aux_data: AD,
    pub transcript_params: &'a T::Params,

    pub g2_elements: Option<[E::G2Affine; 2]>,

    pub _m: std::marker::PhantomData<WP>,
}

impl<'a, E: RescueEngine, P: OldCSParams<E>, WP: WrappedAffinePoint<'a, E>, AD: AuxData<E>, T: ChannelGadget<E>> Circuit<E> 
    for RecursiveAggregationCircuit<'a, E, P, WP, AD, T> 
    where <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>, 
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>    
{
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> 
    { 
        // let num_possible_vks = 1 << self.vk_tree_depth;
        let num_bits_in_proof_id = self.vk_tree_depth;

        let non_residues = make_non_residues::<E::Fr>(P::STATE_WIDTH - 1);

        if let Some(proofs) = self.proofs.as_ref() {
            assert_eq!(self.num_proofs_to_check, proofs.len());
        }

        if let Some(proof_ids) = self.proof_ids.as_ref() {
            assert_eq!(self.num_proofs_to_check, proof_ids.len());
        }

        if let Some(vk_witnesses) = self.vk_witnesses.as_ref() {
            assert_eq!(self.num_proofs_to_check, vk_witnesses.len());
        }

        // Allocate everything, get fs scalar for aggregation

        let mut proof_witnesses = vec![];

        let mut fs_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let proof_witness = self.proofs.as_ref().map(|el| el[proof_index].clone());

            if let Some(proof) = proof_witness.as_ref() {
                assert_eq!(proof.input_values.len(), self.num_inputs, "proof has too many inputs");
                // assert!(proof.input_values.len() <= self.num_inputs, "proof has too many inputs");
            }

            let allocated_proof = ProofGadget::<E, WP>::alloc_from_witness(
                cs, 
                self.num_inputs, 
                &proof_witness, 
                self.rns_params, 
                &self.aux_data
            )?;

            let as_num_witness = allocated_proof.into_witness(cs)?;
            fs_witnesses.extend(as_num_witness);

            proof_witnesses.push(allocated_proof);
        }

        let mut vk_witnesses = vec![];

        let mut vk_leaf_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let vk_witness = self.vk_witnesses.as_ref().map(
                |el| el[proof_index].into_witness_for_params(self.rns_params).expect("must transform into limbed witness")
            );

            let mut allocated = vec![];

            let expected_witness_size = VerificationKey::<E, P>::witness_size_for_params(self.rns_params);

            if let Some(vk_witness) = vk_witness.as_ref() {
                assert_eq!(vk_witness.len(), expected_witness_size, "witness size is not sufficient to create verification key");
            }

            for idx in 0..expected_witness_size {
                let wit = vk_witness.as_ref().map(|el| el[idx]);
                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(*wit.get()?)
                    }
                )?;

                allocated.push(num);
            }

            let domain_size = &allocated[0];
            let omega = &allocated[1];
            let key = &allocated[2..];

            let allocated_vk = VerificationKeyGagdet::<E, WP>::alloc_from_limbs_witness::<_, P, AD>(
                cs, 
                self.num_inputs, 
                domain_size,
                omega,
                key, 
                self.rns_params, 
                non_residues.clone(),
                &self.aux_data
            )?;

            vk_witnesses.push(allocated_vk);

            vk_leaf_witnesses.push(allocated);
        }

        // proofs and verification keys are allocated, not proceed with aggregation

        // first get that FS scalar

        let mut sponge = StatefulRescueGadget::<E>::new(self.rescue_params);

        for w in fs_witnesses.into_iter() {
            sponge.absorb_single_value(cs, w, self.rescue_params)?;
        }

        sponge.pad_if_necessary(self.rescue_params)?;

        let aggregation_challenge = sponge.squeeze_out_single(cs, self.rescue_params)?.into_allocated_num(cs)?;

        // then perform individual aggregation

        let mut pairs_for_generator = vec![];
        let mut pairs_for_x = vec![];

        for proof_idx in 0..self.num_proofs_to_check {
            let proof = &proof_witnesses[proof_idx];
            let vk = &vk_witnesses[proof_idx];
            let [pair_with_generator, pair_with_x] = aggregate_proof::<_, _, T, CS::Params, P, _, _>(
                cs,
                self.transcript_params,
                &proof.input_values,
                &vk,
                &proof,
                &self.aux_data,
                self.rns_params,
            )?;

            dbg!(pair_with_generator.get_point().get_value());
            dbg!(pair_with_x.get_point().get_value());

            pairs_for_generator.push(pair_with_generator);
            pairs_for_x.push(pair_with_x);
        }

        // now make scalars for separation

        let mut scalars = vec![];
        scalars.push(aggregation_challenge.clone());

        let mut current = aggregation_challenge.clone();
        for _ in 1..self.num_proofs_to_check {
            let new = current.mul(cs, &aggregation_challenge)?;
            scalars.push(new.clone());

            current = new;
        }

        // perform final aggregation

        let pair_with_generator = WP::multiexp(cs, &scalars, &pairs_for_generator, None, self.rns_params, &self.aux_data)?;
        let pair_with_x = WP::multiexp(cs, &scalars, &pairs_for_x, None, self.rns_params, &self.aux_data)?;

        match (pair_with_generator.get_point().get_value(), pair_with_x.get_point().get_value(), self.g2_elements) {
            (Some(with_gen), Some(with_x), Some(g2_elements)) => {
                use franklin_crypto::bellman::pairing::ff::Field;

                let valid = E::final_exponentiation(
                    &E::miller_loop(&[
                        (&with_gen.prepare(), &g2_elements[0].prepare()),
                        (&with_x.prepare(), &g2_elements[1].prepare())
                    ])
                ).unwrap() == E::Fqk::one();

                dbg!(valid);
                // assert!(valid);
            },
            _ => {}
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use franklin_crypto::plonk::circuit::verifier_circuit::test::*;
    use franklin_crypto::bellman::pairing::bn256::{Bn256, Fr};
    use franklin_crypto::bellman::pairing::ff::*;
    use franklin_crypto::plonk::circuit::*;

    use franklin_crypto::bellman::pairing::{
        Engine,
        CurveAffine,
        CurveProjective
    };

    use franklin_crypto::bellman::pairing::ff::{
        Field,
        PrimeField,
        BitIterator,
        ScalarEngine,
    };

    use franklin_crypto::bellman::{
        SynthesisError,
    };

    use franklin_crypto::bellman::plonk::better_better_cs::cs::{
        Variable, 
        ConstraintSystem,
    };

    use franklin_crypto::bellman::plonk::better_cs::keys::{Proof, VerificationKey, SetupPolynomialsPrecomputations, SetupPolynomials};
    use franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
    use franklin_crypto::bellman::plonk::better_cs::cs::Circuit as OldCircuit;
    use franklin_crypto::bellman::plonk::better_cs::cs::ConstraintSystem as OldConstraintSystem;
    use franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;
    use franklin_crypto::bellman::plonk::better_cs::generator::GeneratorAssembly as OldAssembly;
    use franklin_crypto::bellman::plonk::better_cs::generator::GeneratorAssembly4WithNextStep as OldActualAssembly;
    use franklin_crypto::bellman::plonk::better_cs::prover::ProverAssembly as OldProver;
    use franklin_crypto::bellman::plonk::better_cs::prover::ProverAssembly4WithNextStep as OldActualProver;


    use franklin_crypto::bellman::plonk::better_cs::verifier::verify_and_aggregate;
    use franklin_crypto::bellman::worker::*;
    use franklin_crypto::bellman::plonk::commitments::transcript::*;
    use franklin_crypto::bellman::kate_commitment::*;
    use franklin_crypto::bellman::plonk::fft::cooley_tukey_ntt::*;
    use franklin_crypto::bellman::plonk::better_better_cs::cs::{
        TrivialAssembly, 
        Circuit, 
        PlonkCsWidth4WithNextStepParams, 
        Width4MainGateWithDNext
    };

    use franklin_crypto::plonk::circuit::curve::sw_affine::*;
    use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::without_flag_unchecked::*;
    use franklin_crypto::plonk::circuit::bigint::field::*;
    use franklin_crypto::plonk::circuit::rescue::*;
    use franklin_crypto::rescue::RescueEngine;
    use franklin_crypto::rescue::bn256::*;
    use franklin_crypto::rescue::rescue_transcript::RescueTranscriptForRNS;
    use franklin_crypto::bellman::plonk::commitments::transcript::Transcript;
    
    #[test]
    fn test_two_proofs() {
        let a = Fr::one();
        let b = Fr::one();
    
        let num_steps = 40;
        let circuit_0 = BenchmarkCircuit::<Bn256> {
            num_steps,
            a,
            b,
            output: fibbonacci(&a, &b, num_steps),
            _engine_marker: std::marker::PhantomData,
        };

        let num_steps = 18;

        let circuit_1 = BenchmarkCircuit::<Bn256> {
            num_steps,
            a,
            b,
            output: fibbonacci(&a, &b, num_steps),
            _engine_marker: std::marker::PhantomData,
        };

        let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
        let rescue_params = Bn256RescueParams::new_checked_2_into_1();

        let transcript_params = (&rescue_params, &rns_params);

        let (vk_0, proof_0) = make_vk_and_proof::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit_0, transcript_params);
        let (vk_1, proof_1) = make_vk_and_proof::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit_1, transcript_params);

        let worker = Worker::new();
        let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(32, &worker);

        let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
        g2_bases.copy_from_slice(&crs_mons.g2_monomial_bases.as_ref()[..]);

        let aux_data = BN256AuxData::new();

        let recursive_circuit = RecursiveAggregationCircuit::<Bn256, OldActualParams, WrapperUnchecked<Bn256>, _, RescueChannelGadget<Bn256>>
        {
            num_proofs_to_check: 2,
            num_inputs: 3,
            vk_tree_depth: 1,
            vk_root: None,
            vk_witnesses: Some(vec![vk_0, vk_1]),
            proof_ids: None,
            proofs: Some(vec![proof_0, proof_1]),
            rescue_params: &rescue_params,
            rns_params: &rns_params,
            aux_data,
            transcript_params: &rescue_params,
        
            g2_elements: Some(g2_bases),
        
            _m: std::marker::PhantomData,
        };

        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        recursive_circuit.synthesize(&mut cs).expect("should synthesize");
        println!("Raw number of gates: {}", cs.n());
        cs.finalize();
        println!("Padded number of gates: {}", cs.n());
        assert!(cs.is_satisfied());
    }

    fn make_vk_and_proof<'a, E: Engine, T: Transcript<E::Fr>>(
        circuit: BenchmarkCircuit<E>, 
        transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
    ) -> (VerificationKey<E, OldActualParams>, Proof<E, OldActualParams>) {
        let worker = Worker::new();
        let mut assembly = OldActualAssembly::<E>::new();
        circuit.clone().synthesize(&mut assembly).expect("should synthesize");
        assembly.finalize();
        let setup = assembly.setup(&worker).expect("should setup");

        let crs_mons = Crs::<E, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals = Crs::<E, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        let verification_key = VerificationKey::from_setup(
            &setup, 
            &worker, 
            &crs_mons
        ).expect("should create vk");

        let precomputations = SetupPolynomialsPrecomputations::from_setup(
            &setup, 
            &worker
        ).expect("should create precomputations");

        let mut prover = OldActualProver::<E>::new();
        circuit.synthesize(&mut prover).expect("should synthesize");
        prover.finalize();

        let size = setup.permutation_polynomials[0].size();

        let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed = 
            <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(size.next_power_of_two());

        println!("BEFORE PROVE");

        let proof = prover.prove::<T, _, _>(
            &worker,
            &setup,
            &precomputations,
            &crs_vals,
            &crs_mons,
            &omegas_bitreversed,
            &omegas_inv_bitreversed,
            Some(transcript_params.clone()),
        ).expect("should prove");

        println!("DONE");

        let (is_valid, [for_gen, for_x]) = verify_and_aggregate::<_, _, T>(&proof, &verification_key, Some(transcript_params)).expect("should verify");

        assert!(is_valid);

        println!("PROOF IS VALID");

        (verification_key, proof)
    }
}