use std::marker::PhantomData;
use num::Float;
use rand::{
    thread_rng,
    Rng,
    distributions::{
        Normal,
        Distribution,
    },
};

struct Layer {
    num_inputs: usize,
    neurons: Vec<Neuron<f64, Sigmoid>>,
}

fn sample(normal: &Normal) -> f64 {
    normal.sample(&mut thread_rng())
}

impl Layer {
    fn new(num_inputs: usize, size: usize, normal: &Normal) -> Self {
        let neurons = (0..size).map(|_| {
            let weights = (0..num_inputs).map(|_| sample(normal)).collect();
            let bias = sample(normal);
            Neuron::new(weights, bias)
        }).collect();
        Self { num_inputs, neurons }
    }

    fn apply(&self, inputs: &[f64]) -> Vec<f64> {
        self.neurons.iter().map(|n| n.apply(inputs)).collect()
    }
}

pub struct Network {
    // First layer is input, last is output, rest are hidden
    layers: Vec<Layer>,
    num_inputs: usize,
}

impl Network {
    fn new(layer_sizes: Vec<usize>) -> Self {
        let normal = Normal::new(0.0, 1.0);
        let layers = layer_sizes.iter()
            .zip(layer_sizes.iter().skip(1))
            .map(|(num_inputs, size)| {
                Layer::new(*num_inputs, *size, &normal)
            })
            .collect();
        Self {
            layers,
            num_inputs: layer_sizes[0],
        }
    }

    fn apply(&self, mut inputs: Vec<f64>) -> Vec<f64> {
        for layer in &self.layers {
            inputs = layer.apply(&inputs);
        }
        inputs
    }
}

fn dot_product<A: Float>(xs: &[A], ys: &[A]) -> A {
    // Since std::iter::Sum is not implemented for num::Float...
    let mut sum = A::zero();
    for (x, y) in xs.iter().zip(ys) {
        sum = (*x).mul_add(*y, sum);
    }
    sum
}

pub trait OutputFn<A: Float> {
    fn output(z: A) -> A;
}

pub struct Sigmoid;

impl <A: Float> OutputFn<A> for Sigmoid {
    fn output(z: A) -> A {
        (A::one() + (-z).exp()).recip()
    }
}

pub struct Perceptron;

impl <A: Float> OutputFn<A> for Perceptron {
    fn output(z: A) -> A {
        if z.is_sign_positive() {
            A::one()
        } else {
            A::zero()
        }
    }
}

pub struct Neuron<A: Float, F: OutputFn<A>> {
    weights: Vec<A>,
    bias: A,
    f_phantom: PhantomData<F>,
}

impl <A: Float, F: OutputFn<A>> Neuron<A, F> {
    fn new(weights: Vec<A>, bias: A) -> Self {
        Self {
            weights,
            bias,
            f_phantom: PhantomData,
        }
    }

    // Not checked strictly.
    fn dimension(&self) -> usize {
        self.weights.len()
    }

    fn apply(&self, inputs: &[A]) -> A {
        let r = dot_product(&self.weights, inputs) + self.bias;
        F::output(r)
    }
}

// SGD and backprop

struct TrainingData {
    inputs: Vec<f64>,
    expected_outputs: Vec<f64>,
}

fn sgd(mut training_data: Vec<TrainingData>,
       num_epoch: usize /* num iterations */,
       mini_batch_size: usize,
       eta: f64 /* learning rate */) {
    let n = training_data.len();
    for _ in 0..num_epoch {
        thread_rng().shuffle(&mut training_data);
    }
}

fn update_mini_batch(mini_batch: &[TrainingData],
                     eta: f64,
                     nw: &mut Network) {
    // nw.layers.map(|layer| vec![0.; layer.neurons
}

#[test]
fn test_perceptron() {
    let p = Neuron::<f32, Perceptron>::new(vec![1., 2.], -4.);
    assert_eq!(2, p.dimension());
    assert_eq!(1., p.apply(&[1., 2.]));
    assert_eq!(0., p.apply(&[1., 1.]));
}

#[test]
fn test_sigmoid() {
    let p = Neuron::<f32, Sigmoid>::new(vec![1., 2.], -4.);
    let passed = p.apply(&[1., 2.]);
    assert!(passed > 0.5);
    assert!(passed < 1.);
    let failed = p.apply(&[1., 1.]);
    assert!(failed < 0.5);
    assert!(failed > 0.);
}

#[test]
fn test_network() {
    let n = Network::new(vec![2, 10, 2]);
    let res = n.apply(vec![0.0, 1.0]);
    let fst = res[0];
    assert!(0. < fst && fst < 1.);
}
