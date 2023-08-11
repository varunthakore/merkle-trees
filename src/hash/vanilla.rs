use ff::PrimeField;
use neptune::poseidon::PoseidonConstants;
use neptune::Arity;

use neptune::sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    vanilla::{Mode, Sponge, SpongeTrait},
};

// Vanilla hash function
pub fn hash<F: PrimeField, A: Arity<F>>(input: Vec<F>, p: &PoseidonConstants<F, A>) -> F {
    let parameter = IOPattern(vec![
        SpongeOp::Absorb(input.len() as u32),
        SpongeOp::Squeeze(1),
    ]);
    let mut sponge = Sponge::new_with_constants(p, Mode::Simplex);
    let acc = &mut ();

    sponge.start(parameter, None, acc);
    SpongeAPI::absorb(&mut sponge, input.len() as u32, &input, acc);

    let output = SpongeAPI::squeeze(&mut sponge, 1, acc);
    assert_eq!(output.len(), 1);

    sponge.finish(acc).unwrap();

    output[0]
}
