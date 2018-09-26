use ndarray::{
    Zip,
    Array,
    ArrayD,
    Array1,
    Array2,
};
use ndarray_rand::{
    F32,
    RandomExt,
};

use rand::{
    thread_rng,
    Rng,
    distributions::{
        Normal,
        // Distribution,
    },
};

use super::network::{
    OutputFn,
    Sigmoid,
};

type FloNum = f32;
type Mat = Array2<FloNum>;
type Arr = Array1<FloNum>;
type ArrD = ArrayD<FloNum>;

struct Network {
    sizes: Array1<usize>,
    weights: Array1<Mat>,
    biases: Array1<Arr>,
}

struct TrainingData {
    inputs: Arr,
    expected_outputs: Arr,
}

struct Deltas {
    weights: Array1<ArrD>,
    biases: Array1<ArrD>,
}

impl Network {
    pub fn new(layer_sizes: Array1<usize>) -> Self {
        let normal = F32(Normal::new(0., 1.));

        let weights = {
            let input_output_counts = layer_sizes.iter()
                .zip(layer_sizes.iter().skip(1));
            input_output_counts.map(|(ins, outs)| {
                Array::random((*outs, *ins), normal)
            }).collect()
        };

        let biases = layer_sizes.iter()
            .skip(1)
            .map(|layer_size| {
                Array::random(*layer_size, normal)
            }).collect();

        Self {
            sizes: layer_sizes,
            weights,
            biases,
        }
    }

    pub fn num_layers(&self) -> usize {
        self.sizes.len()
    }

    pub fn feedforward(&self, mut inputs: Arr) -> Arr {
        for (b, w) in self.biases.iter().zip(self.weights.iter()) {
            let mut outputs = w.dot(&inputs) + b;
            outputs.mapv_inplace(sigmoid);
            inputs = outputs;
        }
        inputs
    }

    pub fn sgd(&mut self,
               mut training_data: Vec<TrainingData>,
               num_epoch: usize /* num iterations */,
               mini_batch_size: usize,
               eta: FloNum /* learning rate */) {
        let n = training_data.len();
        for _ in 0..num_epoch {
            // This requires training_data to be a continuous memory so
            // we had to use Vec rather than Array1.
            thread_rng().shuffle(&mut training_data);
            let mini_batches = training_data.chunks(mini_batch_size);
            for mini_batch in mini_batches {
                self.update_mini_batch(mini_batch, eta);
            }
        }
    }

    fn update_mini_batch(&mut self,
                         mini_batch: &[TrainingData],
                         eta: FloNum) {
        // Hmm... Do we have a easier way to make zero copies?
        let mut nabla_b: Array1<ArrD> = self.biases
            .map(|b| ArrayD::zeros(b.shape()));
        let mut nabla_w: Array1<ArrD> = self.weights
            .map(|w| ArrayD::zeros(w.shape()));

        // Do backprop
        for data in mini_batch {
            let deltas = self.backprop(data);
            Zip::from(&mut nabla_b).and(&deltas.biases).apply(|b, d| {
                *b += d;
            });
            Zip::from(&mut nabla_w).and(&deltas.weights).apply(|w, d| {
                *w += d;
            });
        }
        
        // Write back
        let batch_size = mini_batch.len() as FloNum;
        let scale = -(eta / batch_size);
        Zip::from(&mut self.biases).and(&nabla_b).apply(|b, nb| {
            b.scaled_add(scale, nb);
        });
        Zip::from(&mut self.weights).and(&nabla_w).apply(|w, nw| {
            w.scaled_add(scale, nw);
        });
    }

    fn backprop(&mut self, data: &TrainingData) -> Deltas {
        let x = &data.inputs;
        let y = &data.expected_outputs;

        let mut nabla_b: Array1<ArrD> = self.biases
            .map(|b| ArrayD::zeros(b.shape()));
        let mut nabla_w: Array1<ArrD> = self.weights
            .map(|w| ArrayD::zeros(w.shape()));

        let mut activations = vec![x.clone()];
        let mut zs = vec![];
        Zip::from(&self.biases).and(&self.weights).apply(|b, w| {
            let z = {
                let last = activations.last().unwrap();
                w.dot(last) + b
            };
            let activation = z.mapv(sigmoid);
            zs.push(z);
            activations.push(activation);
        });

        let cd = self.cost_derivative(activations.last().unwrap(), y);
        let delta = cd * zs.last().unwrap().mapv(sigmoid_prime);
        let nabla_w_len = nabla_w.len();
        let activations_len = activations.len();
        nabla_w[nabla_w_len - 1] = delta.dot(&activations[activations_len - 2].t());
        let nabla_b_len = nabla_b.len();
        nabla_b[nabla_b_len - 1] = delta.into_dyn();

        panic!();
    }

    fn cost_derivative(&self, output_activations: &Arr, y: &Arr) -> Arr {
        output_activations - y
    }
}

fn sigmoid(z: FloNum) -> FloNum {
    Sigmoid::output(z)
}

fn sigmoid_prime(z: FloNum) -> FloNum {
    let sz = sigmoid(z);
    sz * (1. - sz)
}

#[test]
fn test_network() {
    let n = Network::new(array![2, 10, 2]);
    let res = n.feedforward(array![0.0, 1.0]);
    let fst = res[0];
    assert!(0. < fst && fst < 1.);
}
