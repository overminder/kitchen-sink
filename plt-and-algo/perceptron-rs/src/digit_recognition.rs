use num::Float;
// use num::cast::NumCast;

fn output_kinds() -> Vec<usize> {
    (0..10).collect()
}

fn desired_output<A: Float>(nth: usize) -> Vec<A> {
    let mut res = vec![A::zero(); 10];
    res[nth] = A::one();
    res
}

fn distance_pow2<A: Float>(xs: &[A], ys: &[A]) -> A {
    let mut sum = A::zero();
    for (x, y) in xs.iter().zip(ys) {
        sum = sum + (*x - *y).powi(2);
    }
    sum
}

fn cost<A: Float>(num_inputs: usize, outputs: &[A]) -> A {
    let mut sum = A::zero();
    for output in output_kinds() {
        sum = sum + distance_pow2(&desired_output(output), outputs);
    }
    let over = A::from(2 * num_inputs).unwrap();  // XXX avoid this?
    sum / over
}

#[test]
fn test_cost() {
    assert_eq!(9., cost(1, &desired_output(0)));
}

