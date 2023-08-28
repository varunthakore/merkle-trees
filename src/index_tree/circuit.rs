use ff::{PrimeField, PrimeFieldBits};
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Strength};

use bellpepper::gadgets::{boolean::{AllocatedBit, Boolean}, num::AllocatedNum};
use bellpepper_core::{Namespace, ConstraintSystem, SynthesisError};

use bellpepper_nonnative::mp::bignat::BigNat;
use bellpepper_nonnative::util::num::Num;
use num_bigint::BigInt;

use crate::{
    hash::circuit::hash_circuit,
    index_tree::tree::{idx_to_bits, Leaf},
};

use super::tree::IndexTree;
use std::marker::PhantomData;

// Code adapted from https://github.com/iden3/circomlib/blob/cff5ab6288b55ef23602221694a6a38a0239dcc0/circuits/comparators.circom#L89
// Outputs true if in1 < in2, otherwise false
pub fn is_less<F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    in1: AllocatedNum<F>,
    in2: AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    let in1_big = BigNat::from_num(
        &mut cs.namespace(|| "input 1 bignat"),
        Num::from(in1.clone()),
        128,
        2,
    )?;
    let in2_big = BigNat::from_num(
        &mut cs.namespace(|| "input 2 bignat"),
        Num::from(in2.clone()),
        128,
        2,
    )?;
    let exp255 = BigNat::alloc_from_nat(
        &mut cs.namespace(|| "exp255 bignat"),
        || Ok(BigInt::from(2u64).pow(255)),
        128,
        2,
    )?;
    let diff = BigNat::sub(
        &BigNat::add::<CS>(&in1_big, &exp255)?,
        &mut cs.namespace(|| "sub"),
        &in2_big,
    )?;

    let diff_bits_var = diff.decompose(&mut cs.namespace(|| "decompose into bits"))?;
    assert_eq!(diff_bits_var.allocations.len(), 256);
    let last_bit = AllocatedBit::alloc(
        &mut cs.namespace(|| "alloc last bit"),
        diff_bits_var.allocations[255].value,
    )?;
    Ok(Boolean::from(last_bit).not())
}

#[derive(Clone)]
pub struct AllocatedLeaf<F: PrimeField + PrimeFieldBits, A: Arity<F>> {
    pub value: AllocatedNum<F>,
    pub next_value: AllocatedNum<F>,
    pub next_index: AllocatedNum<F>,
    pub leaf: Leaf<F, A>,
}

impl<F, A> AllocatedLeaf<F, A>
where
    F: PrimeField + PrimeFieldBits,
    A: Arity<F>,
{
    pub fn alloc_leaf_to_vec(&self) -> Vec<AllocatedNum<F>> {
        let mut input: Vec<AllocatedNum<F>> = vec![];
        input.push(self.value.clone());
        input.push(self.next_value.clone());
        input.push(self.next_index.clone());

        assert_eq!(input.len(), 3);
        // input = [value, next_value, next_index]
        input
    }

    pub fn alloc_leaf<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        leaf: Leaf<F, A>,
    ) -> AllocatedLeaf<F, A> {
        AllocatedLeaf {
            value: AllocatedNum::alloc(cs.namespace(|| "leaf value"), || Ok(leaf.value.unwrap()))
                .unwrap(),
            next_value: AllocatedNum::alloc(cs.namespace(|| "next value"), || {
                Ok(leaf.next_value.unwrap())
            })
            .unwrap(),
            next_index: AllocatedNum::alloc(cs.namespace(|| "next index value"), || {
                Ok(leaf.next_index.unwrap())
            })
            .unwrap(),
            leaf: leaf,
        }
    }
}

pub fn is_member<
    F: PrimeField + PrimeFieldBits,
    AL: Arity<F>,
    AN: Arity<F>,
    const N: usize,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    root_var: AllocatedNum<F>,
    leaf_var: AllocatedLeaf<F, AL>,
    mut idx_var: Vec<AllocatedBit>,
    siblings_var: Vec<AllocatedNum<F>>,
) -> Result<Boolean, SynthesisError> {
    let val_var = AllocatedLeaf::alloc_leaf_to_vec(&leaf_var);
    assert_eq!(val_var.len(), 3);
    assert_eq!(idx_var.len(), N);
    assert_eq!(idx_var.len(), siblings_var.len());

    let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
    let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -1 :"),
        val_var,
        &leaf_hash_params,
    )?;

    idx_var.reverse(); // Going from leaf to root

    for (i, sibling) in siblings_var.clone().into_iter().rev().enumerate() {
        let (lc, rc) = AllocatedNum::conditionally_reverse(
            &mut cs.namespace(|| format!("rev num {} :", i)),
            &cur_hash_var,
            &sibling,
            &Boolean::from(idx_var[i].clone()),
        )?;
        cur_hash_var = hash_circuit(
            &mut cs.namespace(|| format!("hash num {} :", i)),
            vec![lc, rc],
            &node_hash_params,
        )?;
    }

    let is_valid = AllocatedBit::alloc(
        cs.namespace(|| "is member"),
        Some(root_var.get_value() == cur_hash_var.get_value()),
    )?;

    Ok(Boolean::from(is_valid))
}

pub fn is_non_member<
    F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits + PartialOrd,
    AL: Arity<F>,
    AN: Arity<F>,
    const N: usize,
    CS: ConstraintSystem<F>,
>(
    mut cs: CS,
    root_var: AllocatedNum<F>,
    tree: IndexTree<F, N, AL, AN>,
    new_value: AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    // Get low leaf
    let (low_leaf, low_index_int) = tree.get_low_leaf(new_value.get_value());
    let low_leaf_var: AllocatedLeaf<F, AL> = AllocatedLeaf::alloc_leaf(&mut cs, low_leaf);
    let low_leaf_idx = idx_to_bits(N, F::from(low_index_int));
    let low_leaf_siblings = tree.get_siblings_path(low_leaf_idx.clone()).siblings;

    let low_leaf_siblings_var: Vec<AllocatedNum<F>> = low_leaf_siblings
        .into_iter()
        .enumerate()
        .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("sibling {}", i)), || Ok(s)))
        .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

    let low_leaf_idx_var: Vec<AllocatedBit> = low_leaf_idx
        .into_iter()
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("idx {}", i)), Some(b)))
        .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()?;

    // check that low_leaf_var is_member
    let is_member = Boolean::from(is_member::<F, AL, AN, N, CS>(
        &mut cs,
        root_var.clone(),
        low_leaf_var.clone(),
        low_leaf_idx_var.clone(),
        low_leaf_siblings_var.clone(),
    )?);
    Boolean::enforce_equal(&mut cs, &is_member, &Boolean::constant(true))?;

    let cond = Boolean::constant(low_leaf_var.next_index.get_value() == Some(F::ZERO)); // Check low leaf is at the very end

    let out1 = {
        // Case when low leaf is at the very end
        // the low leaf is at the very end, so the new_value must be higher than all values in the tree
        // low_leaf.value < new_value
        is_less(
            &mut cs.namespace(|| "low leaf at end - low_leaf.value < new_value"),
            low_leaf_var.value.clone(),
            new_value.clone(),
        )?
    };

    let out2 = {
        // Case when low leaf is not at the very end
        // low_leaf.value < new_value && new_value < low_leaf.next_value
        let cond1 = is_less(
            &mut cs.namespace(|| "low leaf not at end - low_leaf.value < new_value"),
            low_leaf_var.value.clone(),
            new_value.clone(),
        )?;
        let cond2 = is_less(
            &mut cs.namespace(|| "new_value < low_leaf.next_value"),
            new_value.clone(),
            low_leaf_var.next_value.clone(),
        )?;

        Boolean::and(&mut cs, &cond1, &cond2)?
    };

    let and1 = Boolean::and(&mut cs.namespace(|| "cond & out1"), &cond, &out1)?;
    let and2 = Boolean::and(
        &mut cs.namespace(|| "not cond and out2"),
        &cond.not(),
        &out2,
    )?;

    let out = Boolean::and(
        &mut cs.namespace(|| "and1 + and2"),
        &and1.not(),
        &and2.not(),
    )?
    .not();
    Ok(out)
}

// Remeber to check that new_value is_non_member before calling insert
pub fn insert<
    F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits + PartialOrd,
    AL: Arity<F>,
    AN: Arity<F>,
    const N: usize,
    CS: ConstraintSystem<F>,
>(
    mut cs: CS,
    tree: &mut IndexTree<F, N, AL, AN>,
    root_var: AllocatedNum<F>,
    new_val: AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    // Check that leaf at next_insertion_index is empty
    let next_insetion_idx_bits = idx_to_bits(N, tree.next_insertion_idx)
        .into_iter()
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("next idx {}", i)), Some(b)))
        .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()?;
    let next_insertion_index_siblings = tree
        .get_siblings_path(idx_to_bits(N, tree.next_insertion_idx))
        .siblings
        .into_iter()
        .enumerate()
        .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("next sibling {}", i)), || Ok(s)))
        .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;
    let empty_leaf_var = AllocatedLeaf::alloc_leaf::<
        Namespace<'_, F, <CS as ConstraintSystem<F>>::Root>,
    >(&mut cs.namespace(|| "empty leaf"), Leaf::default());
    let check_empty = is_member::<F, AL, AN, N, CS>(
        &mut cs,
        root_var.clone(),
        empty_leaf_var,
        next_insetion_idx_bits,
        next_insertion_index_siblings,
    )?;
    Boolean::enforce_equal(&mut cs, &check_empty, &Boolean::constant(true))?;

    // Get low leaf
    let (low_leaf, low_index_int) = tree.get_low_leaf(new_val.get_value());

    let mut low_leaf_var =
        AllocatedLeaf::alloc_leaf(&mut cs.namespace(|| "alloc low leaf"), low_leaf.clone());

    // Since low_leaf is member is checked while checking new_values is_non_member (before calling insert)
    // No need to check low_leaf is_member again

    // Range check low leaf against new value
    let check_less = is_less(&mut cs, new_val.clone(), low_leaf_var.next_value.clone())?;
    let check_zero = Boolean::from(AllocatedBit::alloc(
        cs.namespace(|| "is zero"),
        Some(low_leaf_var.next_value.get_value() == Some(F::ZERO)),
    )?);
    let check_range1 = Boolean::not(&Boolean::and(
        &mut cs,
        &Boolean::not(&check_less),
        &Boolean::not(&check_zero),
    )?);
    Boolean::enforce_equal(
        &mut cs.namespace(|| "check range 1 equal"),
        &check_range1,
        &Boolean::constant(true),
    )?;

    let check_range2 = is_less(
        &mut cs.namespace(|| "check range 2"),
        low_leaf_var.value.clone(),
        new_val.clone(),
    )?;
    Boolean::enforce_equal(
        &mut cs.namespace(|| "check range 2 equal"),
        &check_range2,
        &Boolean::constant(true),
    )?;

    // Update new leaf pointers
    let new_leaf_var = AllocatedLeaf {
        value: new_val.clone(),
        next_value: low_leaf_var.next_value,
        next_index: low_leaf_var.next_index,
        leaf: Leaf {
            value: new_val.get_value(),
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
            _arity: PhantomData::<AL>,
        },
    };

    // Update low leaf pointers
    low_leaf_var.next_value = new_val.clone();
    low_leaf_var.next_index =
        AllocatedNum::alloc(&mut cs.namespace(|| "alloc next insertion idx"), || {
            Ok(tree.next_insertion_idx.clone())
        })?;
    low_leaf_var.leaf = Leaf {
        value: low_leaf.value,
        next_value: new_val.get_value(),
        next_index: Some(tree.next_insertion_idx),
        _arity: PhantomData::<AL>,
    };

    // Insert new low leaf into tree
    let mut low_leaf_idx = idx_to_bits(N, F::from(low_index_int));
    let mut low_leaf_siblings = tree.get_siblings_path(low_leaf_idx.clone()).siblings;
    low_leaf_idx.reverse(); // Reverse since path was from root to leaf but I am going leaf to root
    let mut cur_low_leaf_hash = hash_circuit(
        &mut cs.namespace(|| "low leaf hash"),
        AllocatedLeaf::alloc_leaf_to_vec(&low_leaf_var),
        &tree.leaf_hash_params,
    )?
    .get_value()
    .unwrap_or(F::ZERO); // default value to pass None
    for (i, d) in low_leaf_idx.iter().enumerate() {
        let sibling = low_leaf_siblings.pop().unwrap();
        let (l, r) = if *d == false {
            // leaf falls on the left side
            (cur_low_leaf_hash, sibling)
        } else {
            // leaf falls on the right side
            (sibling, cur_low_leaf_hash)
        };
        let val = (l, r);
        let l_var = AllocatedNum::alloc(cs.namespace(|| format!("left var {}", i)), || Ok(l))?;
        let r_var = AllocatedNum::alloc(cs.namespace(|| format!("right var {}", i)), || Ok(r))?;
        cur_low_leaf_hash = hash_circuit(
            &mut cs.namespace(|| format!("low node hash {}", i)),
            vec![l_var, r_var],
            &tree.node_hash_params,
        )?
        .get_value()
        .unwrap_or(F::ZERO); // default value to pass None
        tree.hash_db
            .insert(format!("{:?}", cur_low_leaf_hash.clone()), val);
    }
    tree.root = cur_low_leaf_hash;
    tree.inserted_leaves[low_index_int as usize] = low_leaf_var.leaf.clone();

    // Insert new leaf into tree
    let mut new_leaf_idx = idx_to_bits(N, tree.next_insertion_idx); // from root to leaf
    let mut new_leaf_siblings = tree.get_siblings_path(new_leaf_idx.clone()).siblings;
    new_leaf_idx.reverse(); // from leaf to root
    let mut cur_new_leaf_hash = hash_circuit(
        &mut cs.namespace(|| "new leaf hash"),
        AllocatedLeaf::alloc_leaf_to_vec(&new_leaf_var),
        &tree.leaf_hash_params,
    )?
    .get_value()
    .unwrap_or(F::ZERO); // default value to pass None
    for (i, d) in new_leaf_idx.iter().enumerate() {
        let sibling = new_leaf_siblings.pop().unwrap();
        let (l, r) = if *d == false {
            // leaf falls on the left side
            (cur_new_leaf_hash, sibling)
        } else {
            // leaf falls on the right side
            (sibling, cur_new_leaf_hash)
        };
        let val = (l, r);
        let l_var = AllocatedNum::alloc(cs.namespace(|| format!("new left var {}", i)), || Ok(l))?;
        let r_var = AllocatedNum::alloc(cs.namespace(|| format!("new right var {}", i)), || Ok(r))?;
        cur_new_leaf_hash = hash_circuit(
            &mut cs.namespace(|| format!("new node hash {}", i)),
            vec![l_var, r_var],
            &tree.node_hash_params,
        )?
        .get_value()
        .unwrap_or(F::ZERO); // default value to pass None

        tree.hash_db
            .insert(format!("{:?}", cur_new_leaf_hash.clone()), val);
    }
    tree.root = cur_new_leaf_hash;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::index_tree::tree::{idx_to_bits, IndexTree, Leaf};
    use bellpepper_core::{ConstraintSystem, SynthesisError};
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bellpepper::gadgets::num::AllocatedNum;
    use generic_array::typenum::{U2, U3};
    use num_bigint::BigUint;
    use pasta_curves::group::ff::Field;
    use pasta_curves::Fp;
    use std::marker::PhantomData;

    #[test]
    fn test_insert() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let mut tree: IndexTree<Fp, HEIGHT, U3, U2> = IndexTree::new(empty_leaf.clone());
        println!("root is {:?}", tree.root);
        let new_value = Fp::random(&mut rng);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let root_var: AllocatedNum<Fp> =
            AllocatedNum::alloc_input(cs.namespace(|| "root var"), || Ok(tree.root)).unwrap();
        let new_val_var =
            AllocatedNum::alloc(cs.namespace(|| "new value"), || Ok(new_value)).unwrap();
        insert::<Fp, U3, U2, HEIGHT, Namespace<'_, Fp, TestConstraintSystem<_>>>(
            cs.namespace(|| "Insert value"),
            &mut tree,
            root_var,
            new_val_var,
        )
        .unwrap();
        println!("root is {:?}", tree.root);
        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_member() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let mut tree: IndexTree<Fp, HEIGHT, U3, U2> = IndexTree::new(empty_leaf.clone());
        let low_leaf = empty_leaf.clone();
        let new_value = Fp::random(&mut rng);
        let next_insertion_index = tree.next_insertion_idx;
        let next_leaf_idx = idx_to_bits(HEIGHT, next_insertion_index);
        let new_leaf = Leaf {
            value: Some(new_value),
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
            _arity: PhantomData::<U3>,
        };
        let insert_path = tree.get_siblings_path(next_leaf_idx.clone());
        let mut cs = TestConstraintSystem::<Fp>::new();

        // Allocating all variables
        let root_var: AllocatedNum<Fp> =
            AllocatedNum::alloc_input(cs.namespace(|| "root"), || Ok(tree.root)).unwrap();
        let new_val_var =
            AllocatedNum::alloc(&mut cs.namespace(|| "alloc new value"), || Ok(new_value)).unwrap();
        let val_var: AllocatedLeaf<Fp, U3> = AllocatedLeaf::alloc_leaf(&mut cs, new_leaf);
        let siblings_var: Vec<AllocatedNum<Fp>> = insert_path
            .siblings
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("sibling {}", i)), || Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap();
        let idx_var: Vec<AllocatedBit> = next_leaf_idx
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("idx {}", i)), Some(b)))
            .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
            .unwrap();

        // Check new_leaf is_member should be false
        let is_valid = Boolean::from(
            is_member::<Fp, U3, U2, HEIGHT, _>(
                &mut cs.namespace(|| "is_member false"),
                root_var.clone(),
                val_var.clone(),
                idx_var.clone(),
                siblings_var,
            )
            .unwrap(),
        );
        Boolean::enforce_equal(&mut cs, &is_valid, &Boolean::constant(false)).unwrap();

        // Insert new_value
        insert::<Fp, U3, U2, HEIGHT, Namespace<'_, Fp, TestConstraintSystem<_>>>(
            cs.namespace(|| "Insert value"),
            &mut tree,
            root_var,
            new_val_var,
        )
        .unwrap();

        // Allocate new variables
        let new_root_var: AllocatedNum<Fp> =
            AllocatedNum::alloc_input(cs.namespace(|| "new root"), || Ok(tree.root)).unwrap();
        let new_insert_path = tree.get_siblings_path(next_leaf_idx.clone());
        let new_siblings_var: Vec<AllocatedNum<Fp>> = new_insert_path
            .siblings
            .into_iter()
            .enumerate()
            .map(|(i, s)| {
                AllocatedNum::alloc(cs.namespace(|| format!("new sibling {}", i)), || Ok(s))
            })
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap();

        // Check new_leaf is_member should be true
        let is_valid = Boolean::from(
            is_member::<Fp, U3, U2, HEIGHT, _>(
                &mut cs.namespace(|| "is_member true"),
                new_root_var.clone(),
                val_var,
                idx_var,
                new_siblings_var,
            )
            .unwrap(),
        );
        Boolean::enforce_equal(&mut cs, &is_valid, &Boolean::constant(true)).unwrap();

        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_non_member() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let mut tree: IndexTree<Fp, HEIGHT, U3, U2> = IndexTree::new(empty_leaf.clone());

        let low_leaf = empty_leaf.clone();
        let new_value = Fp::random(&mut rng);
        let next_insertion_index = tree.next_insertion_idx;
        let next_leaf_idx = idx_to_bits(HEIGHT, next_insertion_index);

        let new_leaf = Leaf {
            value: Some(new_value),
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
            _arity: PhantomData::<U3>,
        };

        // Insert new_value at next_insertion_index
        tree.insert_vanilla(new_value.clone());

        // Check that new leaf is inseted at next_insertion_index
        let inserted_path = tree.get_siblings_path(next_leaf_idx.clone());
        assert!(inserted_path.is_member_vanilla(
            next_leaf_idx.clone(),
            &new_leaf.clone(),
            tree.root
        ));

        let mut cs = TestConstraintSystem::<Fp>::new();

        // Allocating all variables
        let root_var: AllocatedNum<Fp> =
            AllocatedNum::alloc_input(cs.namespace(|| "root"), || Ok(tree.root)).unwrap();
        let alloc_member =
            AllocatedNum::alloc(&mut cs.namespace(|| "alloc new value"), || Ok(new_value)).unwrap();
        // Check new_leaf is_non_member should be false
        let old_is_non_member =
            is_non_member::<Fp, U3, U2, HEIGHT, Namespace<'_, Fp, TestConstraintSystem<_>>>(
                cs.namespace(|| "check non member should be false"),
                root_var.clone(),
                tree.clone(),
                alloc_member,
            )
            .unwrap();
        Boolean::enforce_equal(&mut cs, &old_is_non_member, &Boolean::constant(false)).unwrap();

        let non_member = Fp::random(&mut rng);
        let alloc_non_member =
            AllocatedNum::alloc(cs.namespace(|| "non member"), || Ok(non_member)).unwrap();
        // Check new_leaf is_non_member should be true
        let new_is_non_member =
            is_non_member::<Fp, U3, U2, HEIGHT, Namespace<'_, Fp, TestConstraintSystem<_>>>(
                cs.namespace(|| "check non member should be true"),
                root_var,
                tree.clone(),
                alloc_non_member,
            )
            .unwrap();
        Boolean::enforce_equal(&mut cs, &new_is_non_member, &Boolean::constant(true)).unwrap();

        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_less() {
        let mut rng = rand::thread_rng();
        let in1 = Fp::random(&mut rng);
        let in2 = Fp::random(&mut rng);

        let mut cs = TestConstraintSystem::<Fp>::new();

        let in1_int = BigUint::from_bytes_le(&in1.to_repr());
        let in2_int = BigUint::from_bytes_le(&in2.to_repr());

        let in1_var: AllocatedNum<Fp> =
            AllocatedNum::alloc(cs.namespace(|| "in1"), || Ok(in1)).unwrap();
        let in2_var: AllocatedNum<Fp> =
            AllocatedNum::alloc(cs.namespace(|| "in2"), || Ok(in2)).unwrap();
        let op = is_less(&mut cs, in1_var, in2_var)
            .unwrap()
            .get_value()
            .unwrap();

        println!("{:?} < {:?} {:?}", in1, in2, op.clone());
        assert_eq!(in1_int < in2_int, op);

        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    }
}
