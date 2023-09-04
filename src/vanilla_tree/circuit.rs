use crate::hash::circuit::hash_circuit;
use bellpepper::gadgets::{boolean::{AllocatedBit, Boolean}, num::AllocatedNum};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Strength};

pub fn path_verify_circuit<
    F: PrimeField + PrimeFieldBits,
    AL: Arity<F>,
    AN: Arity<F>,
    const N: usize,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    root_var: AllocatedNum<F>,
    val_var: Vec<AllocatedNum<F>>,
    mut idx_var: Vec<AllocatedBit>,
    siblings_var: Vec<AllocatedNum<F>>,
) -> Result<AllocatedBit, SynthesisError> {
    let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
    let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -1 :"),
        val_var,
        &leaf_hash_params,
    )
    .unwrap();

    idx_var.reverse(); // Going from leaf to root

    for (i, sibling) in siblings_var.clone().into_iter().rev().enumerate() {
        let (lc, rc) = AllocatedNum::conditionally_reverse(
            &mut cs.namespace(|| format!("rev num {} :", i)),
            &cur_hash_var,
            &sibling,
            &Boolean::from(idx_var[i].clone()),
        )
        .unwrap();
        cur_hash_var = hash_circuit(
            &mut cs.namespace(|| format!("hash num {} :", i)),
            vec![lc, rc],
            &node_hash_params,
        )
        .unwrap();
    }

    let is_valid = AllocatedBit::alloc(
        cs.namespace(|| "is member"),
        Some(root_var.get_value() == cur_hash_var.get_value()),
    )?;

    cs.enforce(
        || "constarint is_valid",
        |lc| lc + is_valid.get_variable(),
        |lc| lc + root_var.get_variable() - cur_hash_var.get_variable(),
        |lc| lc,
    );

    Ok(is_valid)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vanilla_tree::tree::{idx_to_bits, Leaf, MerkleTree};
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::Field;
    use generic_array::typenum::{U1, U2};
    use pasta_curves::Fp;
    use std::marker::PhantomData;

    #[test]
    fn test_path_verify() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf_val = Leaf::default();
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut tree: MerkleTree<Fp, HEIGHT, U1, U2> = MerkleTree::new(empty_leaf_val);

        let test_cases: u64 = 10;

        for j in 0..test_cases {
            let idx = Fp::from(j);
            let idx_in_bits = idx_to_bits(HEIGHT, idx);
            let leaf = Leaf {
                val: vec![Fp::random(&mut rng)],
                _arity: PhantomData,
            };

            let path = tree.get_siblings_path(idx_in_bits.clone());

            // Allocating all variables
            let root_var: AllocatedNum<Fp> =
                AllocatedNum::alloc_input(cs.namespace(|| format!("root {}", j)), || Ok(tree.root))
                    .unwrap();
            let val_var: Vec<AllocatedNum<Fp>> = leaf
                .clone()
                .val
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("{} : leaf vec {}", j, i)), || {
                        Ok(s)
                    })
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();
            let siblings_var: Vec<AllocatedNum<Fp>> = path
                .siblings
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("{} : sibling {}", j, i)), || Ok(s))
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();
            let idx_var: Vec<AllocatedBit> = idx_in_bits
                .clone()
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("{} : idx {}", j, i)), Some(b))
                })
                .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
                .unwrap();
            let is_valid = Boolean::from(
                path_verify_circuit::<Fp, U1, U2, HEIGHT, _>(
                    &mut cs.namespace(|| format!("{} : is_valid false", j)),
                    root_var,
                    val_var.clone(),
                    idx_var.clone(),
                    siblings_var,
                )
                .unwrap(),
            );
            Boolean::enforce_equal(
                &mut cs.namespace(|| format!("{} : enforce false", j)),
                &is_valid,
                &Boolean::constant(false),
            )
            .unwrap();

            // Insert Leaf
            tree.insert(idx_in_bits.clone(), &leaf);

            let new_path = tree.get_siblings_path(idx_in_bits.clone());

            // Allocating New Variables
            let new_root_var: AllocatedNum<Fp> =
                AllocatedNum::alloc_input(cs.namespace(|| format!("new root {}", j)), || {
                    Ok(tree.root)
                })
                .unwrap();
            let new_siblings_var: Vec<AllocatedNum<Fp>> = new_path
                .siblings
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(
                        cs.namespace(|| format!("{} : new sibling {}", j, i)),
                        || Ok(s),
                    )
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();
            let is_valid = Boolean::from(
                path_verify_circuit::<Fp, U1, U2, HEIGHT, _>(
                    &mut cs.namespace(|| format!("{} : is_valid true", j)),
                    new_root_var,
                    val_var,
                    idx_var,
                    new_siblings_var,
                )
                .unwrap(),
            );
            Boolean::enforce_equal(
                &mut cs.namespace(|| format!("{} : enforce true", j)),
                &is_valid,
                &Boolean::constant(true),
            )
            .unwrap();
        }

        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    }
}
