#![allow(dead_code)]

use franklin_crypto::bellman::pairing::ff::*;
use franklin_crypto::bellman::pairing::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::*;
use franklin_crypto::circuit::Assignment;
use franklin_crypto::plonk::circuit::allocated_num::*;
use franklin_crypto::plonk::circuit::linear_combination::*;
use franklin_crypto::plonk::circuit::boolean::*;
use franklin_crypto::plonk::circuit::sha256::sha256 as sha256_circuit_hash;
use franklin_crypto::plonk::circuit::bigint::field::*;
use franklin_crypto::plonk::circuit::rescue::*;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::aux_data::*;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::*;
use franklin_crypto::plonk::circuit::verifier_circuit::channel::*;
use franklin_crypto::plonk::circuit::verifier_circuit::data_structs::*;
use franklin_crypto::plonk::circuit::verifier_circuit::verifying_circuit::aggregate_proof;
use franklin_crypto::rescue::*;

use franklin_crypto::bellman::SynthesisError;

use franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use franklin_crypto::bellman::plonk::better_cs::generator::make_non_residues;
use franklin_crypto::bellman::plonk::better_cs::keys::{Proof, VerificationKey};

use franklin_crypto::bellman::plonk::better_better_cs::trees::binary_tree::*;
use franklin_crypto::bellman::plonk::better_better_cs::trees::tree_hash::BinaryTreeHasher;
use franklin_crypto::plonk::circuit::bigint::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate;

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
    pub vk_auth_paths: Option<Vec<Vec<E::Fr>>>,
    pub proof_ids: Option<Vec<usize>>,
    pub proofs: Option<Vec<Proof<E, P>>>,
    pub rescue_params: &'a E::Params,
    pub rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    pub aux_data: AD,
    pub transcript_params: &'a T::Params,

    pub g2_elements: Option<[E::G2Affine; 2]>,

    pub _m: std::marker::PhantomData<WP>,
}

pub const ALLIGN_FIELD_ELEMENTS_TO_BITS: usize = 256;

impl<
        'a,
        E: RescueEngine,
        P: OldCSParams<E>,
        WP: WrappedAffinePoint<'a, E>,
        AD: AuxData<E>,
        T: ChannelGadget<E>,
    > Circuit<E> for RecursiveAggregationCircuit<'a, E, P, WP, AD, T>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    type MainGate = Width4MainGateWithDNext;

    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(
            vec![
                Self::MainGate::default().into_internal(),
                TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
            ]
        )
    }
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
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

        if let Some(vk_auth_paths) = self.vk_auth_paths.as_ref() {
            assert_eq!(self.num_proofs_to_check, vk_auth_paths.len());
        }

        // Allocate everything, get fs scalar for aggregation

        let mut proof_witnesses = vec![];

        let mut fs_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let proof_witness = self.proofs.as_ref().map(|el| el[proof_index].clone());

            if let Some(proof) = proof_witness.as_ref() {
                assert_eq!(
                    proof.input_values.len(),
                    self.num_inputs,
                    "proof has too many inputs"
                );
                // assert!(proof.input_values.len() <= self.num_inputs, "proof has too many inputs");
            }

            let allocated_proof = ProofGadget::<E, WP>::alloc_from_witness(
                cs,
                self.num_inputs,
                &proof_witness,
                self.rns_params,
                &self.aux_data,
            )?;

            let as_num_witness = allocated_proof.into_witness(cs)?;
            fs_witnesses.extend(as_num_witness);

            proof_witnesses.push(allocated_proof);
        }

        let mut vk_witnesses = vec![];

        let mut vk_leaf_witnesses = vec![];

        for proof_index in 0..self.num_proofs_to_check {
            let vk_witness = self.vk_witnesses.as_ref().map(|el| {
                el[proof_index]
                    .into_witness_for_params(self.rns_params)
                    .expect("must transform into limbed witness")
            });

            let mut allocated = vec![];

            let expected_witness_size =
                VerificationKey::<E, P>::witness_size_for_params(self.rns_params);

            if let Some(vk_witness) = vk_witness.as_ref() {
                assert_eq!(
                    vk_witness.len(),
                    expected_witness_size,
                    "witness size is not sufficient to create verification key"
                );
            }

            for idx in 0..expected_witness_size {
                let wit = vk_witness.as_ref().map(|el| el[idx]);
                let num = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

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
                &self.aux_data,
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

        let aggregation_challenge = sponge
            .squeeze_out_single(cs, self.rescue_params)?
            .into_allocated_num(cs)?;

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

        let pair_with_generator = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_generator,
            None,
            self.rns_params,
            &self.aux_data,
        )?;
        let pair_with_x = WP::multiexp(
            cs,
            &scalars,
            &pairs_for_x,
            None,
            self.rns_params,
            &self.aux_data,
        )?;

        match (
            pair_with_generator.get_point().get_value(),
            pair_with_x.get_point().get_value(),
            self.g2_elements,
        ) {
            (Some(with_gen), Some(with_x), Some(g2_elements)) => {
                let valid = E::final_exponentiation(&E::miller_loop(&[
                    (&with_gen.prepare(), &g2_elements[0].prepare()),
                    (&with_x.prepare(), &g2_elements[1].prepare()),
                ]))
                .unwrap()
                    == E::Fqk::one();

                dbg!(valid);
            }
            _ => {}
        }

        // allocate vk ids

        let mut key_ids = vec![];
        let vk_root = AllocatedNum::alloc(cs, || Ok(*self.vk_root.get()?))?;

        {
            for proof_index in 0..self.num_proofs_to_check {
                let vk_witness = &vk_leaf_witnesses[proof_index];
                let path_witness = self
                    .proof_ids
                    .as_ref()
                    .map(|el| E::Fr::from_str(&el[proof_index].to_string()).unwrap());
                let path_allocated = AllocatedNum::alloc(cs, || Ok(*path_witness.get()?))?;

                let path_bits = path_allocated.into_bits_le(cs, Some(num_bits_in_proof_id))?;

                key_ids.push(path_bits.clone());

                let mut auth_path = vec![];
                for path_idx in 0..self.vk_tree_depth {
                    let auth_witness = self
                        .vk_auth_paths
                        .as_ref()
                        .map(|el| el[proof_index][path_idx]);
                    let auth_allocated = AllocatedNum::alloc(cs, || Ok(*auth_witness.get()?))?;

                    auth_path.push(auth_allocated);
                }

                assert_eq!(auth_path.len(), path_bits.len());

                let leaf_hash = rescue_leaf_hash(cs, vk_witness, self.rescue_params)?;

                let mut current = leaf_hash.clone();

                for (path_bit, auth_path) in path_bits.into_iter().zip(auth_path.into_iter()) {
                    let left =
                        AllocatedNum::conditionally_select(cs, &auth_path, &current, &path_bit)?;
                    let right =
                        AllocatedNum::conditionally_select(cs, &current, &auth_path, &path_bit)?;

                    let node_hash = rescue_node_hash(cs, left, right, self.rescue_params)?;

                    current = node_hash;
                }

                current.enforce_equal(cs, &vk_root)?;
            }
        }

        let mut hash_to_public_inputs = vec![];
        // VKs tree

        hash_to_public_inputs.extend(allocated_num_to_alligned_big_endian(cs, &vk_root)?);

        // first aggregate proof ids into u8
        for proof_idx in 0..self.num_proofs_to_check {
            let mut le_bits = key_ids[proof_idx].to_vec();
            assert!(le_bits.len() < 8);
            le_bits.resize(8, Boolean::constant(false));

            le_bits.reverse();

            hash_to_public_inputs.extend(le_bits);
        }   

        // now aggregate original public inputs
        for proof_idx in 0..self.num_proofs_to_check {
            let allocated_proof = &proof_witnesses[proof_idx];
            for input_idx in 0..self.num_inputs {
                let input = &allocated_proof.input_values[input_idx];
                let serialized = allocated_num_to_alligned_big_endian(cs, input)?;

                hash_to_public_inputs.extend(serialized);
            }            
        }   

        // now serialize field elements as limbs

        hash_to_public_inputs.extend(serialize_point_into_big_endian(cs, &pair_with_generator)?);
        hash_to_public_inputs.extend(serialize_point_into_big_endian(cs, &pair_with_x)?);

        let input_commitment = sha256_circuit_hash(cs, &hash_to_public_inputs)?;

        let keep = bytes_to_keep::<E>();
        assert!(keep <= 32);
        
        // we don't need to reverse again

        let mut lc = LinearCombination::<E>::zero();

        let mut coeff = E::Fr::one();

        for b in input_commitment[(32-keep)*8..].iter().rev() {
            lc.add_assign_boolean_with_coeff(b, coeff);
            coeff.double();
        }

        let as_num = lc.into_allocated_num(cs)?;

        as_num.inputize(cs)?;

        Ok(())
    }
}

fn allocated_num_to_alligned_big_endian<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = el.into_bits_le(cs, None)?;

    assert!(bits.len() < ALLIGN_FIELD_ELEMENTS_TO_BITS);

    bits.resize(ALLIGN_FIELD_ELEMENTS_TO_BITS, Boolean::constant(false));

    bits.reverse();

    Ok(bits)
}

fn debug_print_boolean_array_as_hex(input: &[Boolean]) {
    assert_eq!(input.len() % 8, 0);

    let mut result = vec![];

    for byte in input.chunks(8) {
        let mut byte_value = 0u8;
        for (idx, bit) in byte.iter().enumerate() {
            if let Some(value) = bit.get_value() {
                let base = if value {
                    1u8
                } else {
                    0u8
                };

                byte_value += base << (7-idx);
            } else {
                return;
            }
        }

        result.push(byte_value);
    }

    println!("Value = {}", hex::encode(&result));
}

fn allocated_num_to_big_endian_of_fixed_width<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    el: &AllocatedNum<E>,
    limit: usize
) -> Result<Vec<Boolean>, SynthesisError> {
    let mut bits = el.into_bits_le(cs, Some(limit))?;
    bits.reverse();

    Ok(bits)
}

fn serialize_point_into_big_endian<'a, E: Engine, CS: ConstraintSystem<E>, WP: WrappedAffinePoint<'a, E>>(
    cs: &mut CS,
    point: &WP
) -> Result<Vec<Boolean>, SynthesisError> {
    let raw_point = point.get_point();

    let x = raw_point.get_x().force_reduce_into_field(cs)?.enforce_is_normalized(cs)?;
    let y = raw_point.get_y().force_reduce_into_field(cs)?.enforce_is_normalized(cs)?;

    let mut serialized = vec![];

    for coord in vec![x, y].into_iter() {
        for limb in coord.into_limbs().into_iter() {
            let as_num = limb.into_variable(); // this checks coeff and constant term internally
            serialized.extend(allocated_num_to_alligned_big_endian(cs, &as_num)?);
        }
    }

    Ok(serialized)
}

fn rescue_leaf_hash<E: RescueEngine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    leaf: &[AllocatedNum<E>],
    params: &E::Params,
) -> Result<AllocatedNum<E>, SynthesisError>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    let mut rescue_gadget = StatefulRescueGadget::<E>::new(&params);

    rescue_gadget.specizalize(leaf.len() as u8);
    rescue_gadget.absorb(cs, leaf, params)?;

    let output = rescue_gadget.squeeze_out_single(cs, params)?;

    let as_num = output.into_allocated_num(cs)?;

    Ok(as_num)
}

fn rescue_node_hash<E: RescueEngine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    left: AllocatedNum<E>,
    right: AllocatedNum<E>,
    params: &E::Params,
) -> Result<AllocatedNum<E>, SynthesisError>
where
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox0: PlonkCsSBox<E>,
    <<E as RescueEngine>::Params as RescueHashParams<E>>::SBox1: PlonkCsSBox<E>,
{
    let mut rescue_gadget = StatefulRescueGadget::<E>::new(&params);

    rescue_gadget.specizalize(2);
    rescue_gadget.absorb(cs, &[left, right], params)?;

    let output = rescue_gadget.squeeze_out_single(cs, params)?;

    let as_num = output.into_allocated_num(cs)?;

    Ok(as_num)
}

pub struct StaticRescueBinaryTreeHasher<E: RescueEngine> {
    params: E::Params,
}

impl<E: RescueEngine> StaticRescueBinaryTreeHasher<E> {
    pub fn new(params: &E::Params) -> Self {
        assert_eq!(params.rate(), 2u32);
        assert_eq!(params.output_len(), 1u32);
        Self { params: params.clone() }
    }
}

impl<E: RescueEngine> Clone for StaticRescueBinaryTreeHasher<E> {
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

impl<E: RescueEngine> BinaryTreeHasher<E::Fr> for StaticRescueBinaryTreeHasher<E> {
    type Output = E::Fr;

    #[inline]
    fn placeholder_output() -> Self::Output {
        E::Fr::zero()
    }

    fn leaf_hash(&self, input: &[E::Fr]) -> Self::Output {
        let mut as_vec = rescue_hash::<E>(&self.params, input);

        as_vec.pop().unwrap()
    }

    fn node_hash(&self, input: &[Self::Output; 2], _level: usize) -> Self::Output {
        let mut as_vec = rescue_hash::<E>(&self.params, &input[..]);

        as_vec.pop().unwrap()
    }
}

pub fn make_vks_tree<'a, E: RescueEngine, P: OldCSParams<E>>(
    vks: &[VerificationKey<E, P>],
    params: &'a E::Params,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> (BinaryTree<E, StaticRescueBinaryTreeHasher<E>>, Vec<E::Fr>) {
    let mut leaf_combinations: Vec<Vec<&[E::Fr]>> = vec![vec![]; vks.len()];

    let hasher = StaticRescueBinaryTreeHasher::new(params);
    let mut tmp = vec![];

    for vk in vks.iter() {
        let witness = vk
            .into_witness_for_params(rns_params)
            .expect("must transform into limbed witness");
        tmp.push(witness);
    }

    for idx in 0..vks.len() {
        leaf_combinations[idx].push(&tmp[idx][..]);
    }

    let tree_params = BinaryTreeParams {
        values_per_leaf: VerificationKey::<E, P>::witness_size_for_params(rns_params),
    };

    let tree = BinaryTree::<E, _>::create_from_combined_leafs(
        &leaf_combinations[..],
        1,
        hasher,
        &tree_params,
    );

    let mut all_values = vec![];
    for w in tmp.into_iter() {
        all_values.extend(w);
    }

    (tree, all_values)
}

pub fn make_aggregate<'a, E: RescueEngine, P: OldCSParams<E>>(
    proofs: &[Proof<E, P>],
    vks: &[VerificationKey<E, P>],
    params: &'a E::Params,
    rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> Result<[E::G1Affine; 2], SynthesisError> {
    use franklin_crypto::bellman::plonk::better_cs::verifier::verify_and_aggregate;
    use franklin_crypto::rescue::rescue_transcript::RescueTranscriptForRNS;

    assert_eq!(proofs.len(), vks.len());

    let mut channel = StatefulRescue::<E>::new(params);
    for p in proofs.iter() {
        let as_fe = p.into_witness_for_params(rns_params)?;

        for fe in as_fe.into_iter() {
            channel.absorb_single_value(fe);
        }
    }

    channel.pad_if_necessary();

    let aggregation_challenge: E::Fr = channel.squeeze_out_single();

    let mut pair_with_generator = E::G1::zero();
    let mut pair_with_x = E::G1::zero();

    let mut current = aggregation_challenge;

    for (vk, proof) in vks.iter().zip(proofs.iter()) {
        let (is_valid, [for_gen, for_x]) = verify_and_aggregate::<_, _, RescueTranscriptForRNS<E>>(&proof, &vk, Some((params, rns_params)))
            .expect("should verify");

        assert!(is_valid);

        let contribution = for_gen.mul(current.into_repr());
        pair_with_generator.add_assign(&contribution);

        let contribution = for_x.mul(current.into_repr());
        pair_with_x.add_assign(&contribution);

        current.mul_assign(&aggregation_challenge);
    }

    let pair_with_generator = pair_with_generator.into_affine();
    let pair_with_x = pair_with_x.into_affine();

    assert!(!pair_with_generator.is_zero());
    assert!(!pair_with_x.is_zero());

    Ok([pair_with_generator, pair_with_x])
}

pub fn make_public_input<E: Engine, P: OldCSParams<E>>(
    vks_root: E::Fr,
    proof_indexes: &[usize],
    proofs: &[Proof<E, P>],
    aggregate: &[E::G1Affine; 2],
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> E::Fr {
    use std::io::Write;

    let input = make_public_input_for_hashing(vks_root, proof_indexes, proofs, aggregate, rns_params);

    let mut hash_output = [0u8; 32];

    use sha2::{Sha256, Digest};
    let mut hasher = Sha256::new();
    hasher.update(&input);
    let result = hasher.finalize();

    (&mut hash_output[..]).write(&result.as_slice()).expect("must write");

    let keep = bytes_to_keep::<E>();
    for idx in 0..(32 - keep) {
        hash_output[idx] = 0;
    }

    let mut repr = <E::Fr as PrimeField>::Repr::default();
    repr.read_be(&hash_output[..]).expect("must read BE repr");

    let fe = E::Fr::from_repr(repr).expect("must be valid representation");

    fe
}

fn make_public_input_for_hashing<E: Engine, P: OldCSParams<E>>(
    vks_root: E::Fr,
    proof_indexes: &[usize],
    proofs: &[Proof<E, P>],
    aggregate: &[E::G1Affine; 2],
    rns_params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
) -> Vec<u8> {
    let mut result = vec![];

    add_field_element(&vks_root, &mut result);
    for idx in proof_indexes.iter() {
        assert!(*idx < 256);
        result.push(*idx as u8);
    }

    for proof in proofs.iter() {
        for input in proof.input_values.iter() {
            add_field_element(input, &mut result);
        }
    }

    add_point(&aggregate[0], &mut result, rns_params);
    add_point(&aggregate[1], &mut result, rns_params);

    result
}

fn bytes_to_keep<E: Engine>() -> usize {
    (E::Fr::CAPACITY / 8) as usize
}

fn add_field_element<F: PrimeField>(src: &F, dst: &mut Vec<u8>) {
    let repr = src.into_repr();

    let mut buffer = [0u8; 32];
    repr.write_be(&mut buffer[..]).expect("must write");

    dst.extend_from_slice(&buffer);
}

fn add_point<E: Engine>(src: &E::G1Affine, dst: &mut Vec<u8>, params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>) {
    use franklin_crypto::plonk::circuit::verifier_circuit::utils::*;

    let mut new_params = params.clone();
    new_params.set_prefer_single_limb_allocation(true);

    let params = &new_params;

    let mut tmp_dest = vec![];
    add_point(src, &mut tmp_dest, &params);

    for p in tmp_dest.into_iter() {
        add_field_element(&p, dst);
    }
}

use franklin_crypto::bellman::plonk::better_better_cs::setup::{
    VerificationKey as NewVerificationKey, Setup as NewSetup,
};

use franklin_crypto::bellman::plonk::better_better_cs::cs::{
    Circuit, SetupAssembly, ProvingAssembly, Width4MainGateWithDNext,
};

use franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;
use franklin_crypto::plonk::circuit::verifier_circuit::affine_point_wrapper::without_flag_unchecked::WrapperUnchecked;
use franklin_crypto::bellman::pairing::bn256::Bn256;
use franklin_crypto::bellman::kate_commitment::*;
use franklin_crypto::plonk::circuit::Width4WithCustomGates;
use franklin_crypto::rescue::bn256::Bn256RescueParams;

pub type RecursiveAggregationCircuitBn256<'a> = RecursiveAggregationCircuit::<'a, Bn256, OldActualParams, WrapperUnchecked<'a, Bn256>, BN256AuxData, RescueChannelGadget<Bn256>>;


pub fn create_recursive_circuit_setup<'a>(
    num_proofs_to_check: usize,
    num_inputs: usize,
    vk_tree_depth: usize,
) -> Result<NewSetup<Bn256, RecursiveAggregationCircuitBn256<'a>>, SynthesisError> {
    let mut assembly = SetupAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

    let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
    let rescue_params = Bn256RescueParams::new_checked_2_into_1();
    let aux_data = BN256AuxData::new();

    // let transcript_params = (&rescue_params, &rns_params);

    let recursive_circuit = RecursiveAggregationCircuitBn256 {
        num_proofs_to_check,
        num_inputs,
        vk_tree_depth,
        vk_root: None,
        vk_witnesses: None,
        vk_auth_paths: None,
        proof_ids: None,
        proofs: None,
        rescue_params: &rescue_params,
        rns_params: &rns_params,
        aux_data,
        transcript_params: &rescue_params,

        g2_elements: None,

        _m: std::marker::PhantomData,
    };

    recursive_circuit.synthesize(&mut assembly)?;

    use franklin_crypto::bellman::worker::*;
    let worker = Worker::new();

    assembly.finalize();
    let setup = assembly.create_setup(&worker)?;

    Ok(setup)
}

pub fn create_recursive_circuit_vk_and_setup<'a>(
    num_proofs_to_check: usize,
    num_inputs: usize,
    vk_tree_depth: usize,
    crs: &Crs<Bn256, CrsForMonomialForm>,
) -> Result<(NewVerificationKey<Bn256, RecursiveAggregationCircuitBn256<'a>>, NewSetup<Bn256, RecursiveAggregationCircuitBn256<'a>>), SynthesisError> {
    use franklin_crypto::bellman::worker::*;
    let worker = Worker::new();

    let setup = create_recursive_circuit_setup(num_proofs_to_check, num_inputs, vk_tree_depth)?;

    let vk = NewVerificationKey::<Bn256, RecursiveAggregationCircuitBn256<'a>>::from_setup(&setup, &worker, &crs)?;

    Ok((vk, setup))
}

pub fn create_vks_tree(
    vks: &[VerificationKey<Bn256, OldActualParams>],
    tree_depth: usize
) -> Result<(usize, (BinaryTree<Bn256, StaticRescueBinaryTreeHasher<Bn256>>, Vec<<Bn256 as ScalarEngine>::Fr>)), SynthesisError> {
    assert!(vks.len() > 0);
    let max_size = 1 << tree_depth;
    assert!(vks.len() <= max_size);

    let max_valid_idx = vks.len() - 1;

    let mut padded = vks.to_vec();
    padded.resize(max_size, vks.last().unwrap().clone());

    let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
    let rescue_params = Bn256RescueParams::new_checked_2_into_1();

    let (tree, witness) = make_vks_tree(&padded, &rescue_params, &rns_params);

    Ok((max_valid_idx, (tree, witness)))
}

#[cfg(test)]
mod test {
    use super::*;

    use franklin_crypto::bellman::pairing::bn256::{Bn256, Fr};
    use franklin_crypto::bellman::pairing::ff::*;
    use franklin_crypto::plonk::circuit::verifier_circuit::test::*;
    use franklin_crypto::plonk::circuit::*;

    use franklin_crypto::bellman::pairing::{CurveAffine, CurveProjective, Engine};

    use franklin_crypto::bellman::pairing::ff::{BitIterator, Field, PrimeField, ScalarEngine};

    use franklin_crypto::bellman::SynthesisError;

    use franklin_crypto::bellman::plonk::better_better_cs::cs::{ConstraintSystem, Variable};

    use franklin_crypto::bellman::plonk::better_cs::cs::Circuit as OldCircuit;
    use franklin_crypto::bellman::plonk::better_cs::cs::ConstraintSystem as OldConstraintSystem;
    use franklin_crypto::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
    use franklin_crypto::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;
    use franklin_crypto::bellman::plonk::better_cs::generator::GeneratorAssembly as OldAssembly;
    use franklin_crypto::bellman::plonk::better_cs::generator::GeneratorAssembly4WithNextStep as OldActualAssembly;
    use franklin_crypto::bellman::plonk::better_cs::keys::{
        Proof, SetupPolynomials, SetupPolynomialsPrecomputations, VerificationKey,
    };
    use franklin_crypto::bellman::plonk::better_cs::prover::ProverAssembly as OldProver;
    use franklin_crypto::bellman::plonk::better_cs::prover::ProverAssembly4WithNextStep as OldActualProver;

    use franklin_crypto::bellman::kate_commitment::*;
    use franklin_crypto::bellman::plonk::better_better_cs::cs::{
        Circuit, PlonkCsWidth4WithNextStepParams, TrivialAssembly, Width4MainGateWithDNext,
    };
    use franklin_crypto::bellman::plonk::better_cs::verifier::verify_and_aggregate;
    use franklin_crypto::bellman::plonk::commitments::transcript::*;
    use franklin_crypto::bellman::plonk::fft::cooley_tukey_ntt::*;
    use franklin_crypto::bellman::worker::*;

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

        let (vk_0, proof_0) =
            make_vk_and_proof::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit_0, transcript_params);
        let (vk_1, proof_1) =
            make_vk_and_proof::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit_1, transcript_params);

        let worker = Worker::new();
        let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(32, &worker);

        let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
        g2_bases.copy_from_slice(&crs_mons.g2_monomial_bases.as_ref()[..]);

        let aux_data = BN256AuxData::new();

        let vks_in_tree = vec![vk_1.clone(), vk_0.clone()];
        // make in reverse
        let (vks_tree, all_witness_values) =
            make_vks_tree(&vks_in_tree, &rescue_params, &rns_params);

        let vks_tree_root = vks_tree.get_commitment();

        let proof_ids = vec![1, 0];

        let mut queries = vec![];
        for idx in 0..2 {
            let proof_id = proof_ids[idx];
            let vk = &vks_in_tree[proof_id];

            let leaf_values = vk
                .into_witness_for_params(&rns_params)
                .expect("must transform into limbed witness");

            let values_per_leaf = leaf_values.len();
            let intra_leaf_indexes_to_query: Vec<_> =
                ((proof_id * values_per_leaf)..((proof_id + 1) * values_per_leaf)).collect();
            let q = vks_tree.produce_query(intra_leaf_indexes_to_query, &all_witness_values);

            assert_eq!(q.values(), &leaf_values[..]);

            queries.push(q.path().to_vec());
        }

        let aggregate = make_aggregate(
            &vec![proof_0.clone(), proof_1.clone()], 
            &vec![vk_0.clone(), vk_1.clone()], 
            &rescue_params,
            &rns_params
        ).unwrap();

        let expected_input = make_public_input(
            vks_tree_root,
            &proof_ids,
            &vec![proof_0.clone(), proof_1.clone()],
            &aggregate,
            &rns_params
        );

        let recursive_circuit = RecursiveAggregationCircuit::<
            Bn256,
            OldActualParams,
            WrapperUnchecked<Bn256>,
            _,
            RescueChannelGadget<Bn256>,
        > {
            num_proofs_to_check: 2,
            num_inputs: 3,
            vk_tree_depth: 1,
            vk_root: Some(vks_tree_root),
            vk_witnesses: Some(vec![vk_0, vk_1]),
            vk_auth_paths: Some(queries),
            proof_ids: Some(proof_ids),
            proofs: Some(vec![proof_0, proof_1]),
            rescue_params: &rescue_params,
            rns_params: &rns_params,
            aux_data,
            transcript_params: &rescue_params,

            g2_elements: Some(g2_bases),

            _m: std::marker::PhantomData,
        };

        let mut cs =
            TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        recursive_circuit
            .synthesize(&mut cs)
            .expect("should synthesize");
        println!("Raw number of gates: {}", cs.n());
        cs.finalize();
        println!("Padded number of gates: {}", cs.n());
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_inputs, 1);
    }

    fn make_vk_and_proof<'a, E: Engine, T: Transcript<E::Fr>>(
        circuit: BenchmarkCircuit<E>,
        transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
    ) -> (
        VerificationKey<E, OldActualParams>,
        Proof<E, OldActualParams>,
    ) {
        let worker = Worker::new();
        let mut assembly = OldActualAssembly::<E>::new();
        circuit
            .clone()
            .synthesize(&mut assembly)
            .expect("should synthesize");
        assembly.finalize();
        let setup = assembly.setup(&worker).expect("should setup");

        let crs_mons =
            Crs::<E, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals =
            Crs::<E, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        let verification_key =
            VerificationKey::from_setup(&setup, &worker, &crs_mons).expect("should create vk");

        let precomputations = SetupPolynomialsPrecomputations::from_setup(&setup, &worker)
            .expect("should create precomputations");

        let mut prover = OldActualProver::<E>::new();
        circuit.synthesize(&mut prover).expect("should synthesize");
        prover.finalize();

        let size = setup.permutation_polynomials[0].size();

        let omegas_bitreversed =
            BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed =
            <OmegasInvBitreversed<E::Fr> as CTPrecomputations<E::Fr>>::new_for_domain_size(
                size.next_power_of_two(),
            );

        println!("BEFORE PROVE");

        let proof = prover
            .prove::<T, _, _>(
                &worker,
                &setup,
                &precomputations,
                &crs_vals,
                &crs_mons,
                &omegas_bitreversed,
                &omegas_inv_bitreversed,
                Some(transcript_params.clone()),
            )
            .expect("should prove");

        println!("DONE");

        let (is_valid, [_for_gen, _for_x]) =
            verify_and_aggregate::<_, _, T>(&proof, &verification_key, Some(transcript_params))
                .expect("should verify");

        assert!(is_valid);

        println!("PROOF IS VALID");

        (verification_key, proof)
    }

    fn open_crs_for_log2_of_size(n: usize) -> Crs::<Bn256, CrsForMonomialForm> {
        let base_path = std::path::Path::new("/Users/alexvlasov/Downloads/setup/processed");
        let full_path = base_path.join(&format!("setup_2^{}.key", n));
        println!("Opening {}", full_path.to_string_lossy());
        let file = std::fs::File::open(full_path).unwrap();
        let reader = std::io::BufReader::with_capacity(1 << 24, file);

        let crs = Crs::<Bn256, CrsForMonomialForm>::read(reader).unwrap();

        crs
    }

    #[test]
    fn create_vk() {
        let crs = open_crs_for_log2_of_size(22);

        // let size = 1 << 22;
        // let worker = Worker::new();
        // let crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(size, &worker);

        let (vk, _) = create_recursive_circuit_vk_and_setup(2, 1, 3, &crs).unwrap();

        dbg!(vk);
    }

    fn make_vk_and_proof_for_crs<'a, E: Engine, T: Transcript<E::Fr>>(
        circuit: BenchmarkCircuitWithOneInput<E>,
        transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
        crs: &Crs::<E, CrsForMonomialForm>,
    ) -> (
        VerificationKey<E, OldActualParams>,
        Proof<E, OldActualParams>,
    ) {
        let worker = Worker::new();
        let mut assembly = OldActualAssembly::<E>::new();
        circuit
            .synthesize(&mut assembly)
            .expect("should synthesize");
        assembly.finalize();
        let setup = assembly.setup(&worker).expect("should setup");

        let verification_key =
            VerificationKey::from_setup(&setup, &worker, &crs).expect("should create vk");

        let proof = franklin_crypto::bellman::plonk::prove_native_by_steps::<E, _, T>(
            &circuit,
            &setup,
            None,
            crs,
            Some(transcript_params.clone())
        ).expect("should create a proof");

        let (is_valid, [_for_gen, _for_x]) =
            verify_and_aggregate::<_, _, T>(&proof, &verification_key, Some(transcript_params))
                .expect("should verify");

        assert!(is_valid);

        (verification_key, proof)
    }

    #[test]
    fn simulate_zksync_proofs() {
        let a = Fr::one();
        let b = Fr::one();

        let mut circuits = vec![];
        for num_steps in vec![18, 40, 25, 35].into_iter() {
            let circuit = BenchmarkCircuitWithOneInput::<Bn256> {
                num_steps,
                a,
                b,
                output: fibbonacci(&a, &b, num_steps),
                _engine_marker: std::marker::PhantomData,
            };

            circuits.push(circuit);
        }


        let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
        let rescue_params = Bn256RescueParams::new_checked_2_into_1();

        let transcript_params = (&rescue_params, &rns_params);

        let crs = open_crs_for_log2_of_size(22);

        let mut vks = vec![];
        let mut proofs = vec![];

        for circuit in circuits.into_iter() {
            let (vk, proof) =
                make_vk_and_proof_for_crs::<Bn256, RescueTranscriptForRNS<Bn256>>(circuit, transcript_params, &crs);

            vks.push(vk);
            proofs.push(proof);
        }

        let num_inputs = 1;
        let num_proofs_to_check = 2;
        let tree_depth = 3;

        let (max_index, (vks_tree, tree_witnesses)) = create_vks_tree(&vks, tree_depth).expect("must create vks tree");

        assert_eq!(max_index, 3);

        let proofs_to_check = vec![2,3];

        let mut queries = vec![];

        let mut proofs_to_aggregate = vec![];
        let mut vks_to_aggregate = vec![];
        for &proof_id in proofs_to_check.iter() {
            let vk = &vks[proof_id];
            let proof = &proofs[proof_id];

            proofs_to_aggregate.push(proof.clone());
            vks_to_aggregate.push(vk.clone());

            let leaf_values = vk
                .into_witness_for_params(&rns_params)
                .expect("must transform into limbed witness");

            let values_per_leaf = leaf_values.len();
            let intra_leaf_indexes_to_query: Vec<_> =
                ((proof_id * values_per_leaf)..((proof_id + 1) * values_per_leaf)).collect();
            let q = vks_tree.produce_query(intra_leaf_indexes_to_query, &tree_witnesses);

            assert_eq!(q.values(), &leaf_values[..]);

            queries.push(q.path().to_vec());
        }

        let aggregate = make_aggregate(
            &proofs_to_aggregate, 
            &vks_to_aggregate, 
            &rescue_params,
            &rns_params
        ).unwrap();

        let vks_tree_root = vks_tree.get_commitment();

        let expected_input = make_public_input(
            vks_tree_root,
            &proofs_to_check,
            &proofs_to_aggregate,
            &aggregate,
            &rns_params
        );

        println!("MAKING VK FOR RECURSIVE CIRCUIT");

        let (vk_for_recursive_circut, setup) = create_recursive_circuit_vk_and_setup(
            num_proofs_to_check,
            num_inputs,
            tree_depth,
            &crs,
        ).expect("must create recursive circuit verification key");

        // let setup = create_recursive_circuit_setup(
        //     num_proofs_to_check,
        //     num_inputs,
        //     tree_depth
        // ).expect("must create recursive circuit verification key");

        assert_eq!(setup.num_inputs, 1);

        println!("RECURSIVE CIRCUIT VK IS COMPLETE");

        assert_eq!(vk_for_recursive_circut.total_lookup_entries_length, 0);

        let mut g2_bases = [<<Bn256 as Engine>::G2Affine as CurveAffine>::zero(); 2];
        g2_bases.copy_from_slice(&crs.g2_monomial_bases.as_ref()[..]);

        let aux_data = BN256AuxData::new();

        let recursive_circuit_with_witness = RecursiveAggregationCircuitBn256 {
            num_proofs_to_check: num_proofs_to_check,
            num_inputs: num_inputs,
            vk_tree_depth: tree_depth,
            vk_root: Some(vks_tree_root),
            vk_witnesses: Some(vks_to_aggregate),
            vk_auth_paths: Some(queries),
            proof_ids: Some(proofs_to_check),
            proofs: Some(proofs_to_aggregate),
            rescue_params: &rescue_params,
            rns_params: &rns_params,
            aux_data,
            transcript_params: &rescue_params,

            g2_elements: Some(g2_bases),

            _m: std::marker::PhantomData,
        };

        // println!("TESTING IF SATISFIED");

        // let mut assembly = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        // recursive_circuit_with_witness.synthesize(&mut assembly).expect("must synthesize");
        // assembly.finalize();
        // assert!(assembly.is_satisfied());

        // println!("DONE TESTING IF SATISFIED");
    
        let worker = Worker::new();

        use franklin_crypto::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;

        println!("MAKING PROOF FOR RECURSIVE CIRCUIT");

        let mut assembly = ProvingAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        recursive_circuit_with_witness.synthesize(&mut assembly).expect("must synthesize");
        assembly.finalize();

        let proof = assembly.create_proof::<_, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
            &worker, 
            &setup, 
            &crs, 
            None
        ).expect("must create a proof");

        println!("PROOF FOR RECURSIVE CIRCUIT IS COMPLETE");

        assert_eq!(proof.inputs[0], expected_input, "expected input is not equal to one in a circuit");

        use franklin_crypto::bellman::plonk::better_better_cs::verifier::verify;

        let is_valid = verify::<_, _, RollingKeccakTranscript<<Bn256 as ScalarEngine>::Fr>>(
            &vk_for_recursive_circut,
            &proof,
            None,
        ).expect("must perform verification");

        assert!(is_valid);
    }
}
