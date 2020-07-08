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

    _m: std::marker::PhantomData<WP>,
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

            for idx in 0..VerificationKey::<E, P>::witness_size_for_params(self.rns_params) {
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

        let aggregation_challenge = sponge.squeeze_out_single(cs, self.rescue_params)?;

        dbg!(aggregation_challenge.get_value());

        // then perform individual aggregation

        let mut pairs_for_generator = vec![];
        let mut pairs_for_x = vec![];

        for proof_idx in 0..self.num_proofs_to_check {
            let proof = &proof_witnesses[proof_idx];
            let vk = &vk_witnesses[proof_idx];
            let [pair_with_generator, pair_with_x] = aggregate_proof::<_, _, T, _, _, _, _, _>(
                cs,
                self.transcript_params,
                &proof.input_values,
                &vk,
                &proof,
                &self.aux_data,
                self.rns_params,
            )?;

            pairs_for_generator.push(pair_with_generator);
            pairs_for_x.push(pair_with_x);
        }

        // now make scalars for separation

        let mut scalars = vec![];
        scalars.push(aggregation_challenge.clone());

        let mut current = aggregation_challenge.clone();
        for _ in 1..self.num_proofs_to_check {
            let new = current.mul(cs, &aggregation_challenge)?;
            scalars.push(new);

            current = new;
        }

        // perform final aggregation

        let pair_with_generator = WP::multiexp(cs, &scalars, pairs_for_generator, None, self.rns_params, self.aux_data)?;
        let pair_with_x = WP::multiexp(cs, &scalars, pairs_for_x, None, self.rns_params, self.aux_data)?;

        Ok(())
    }
}