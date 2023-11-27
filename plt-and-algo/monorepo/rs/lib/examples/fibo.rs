use lib::fibo;
use chrono::Utc;

fn main() {
    bench("fibo_asm", fibo::fibo_asm, 40);
    bench("fibo_rs", fibo::fibo_rs, 40);
    bench("fibo_interp_fast", fibo::fibo_interp_fast, 40);
    bench("fibo_interp_slow", fibo::fibo_interp_slow, 40);
}

fn bench(name: &str, func: fn(i64) -> i64, arg: i64) {
    let t0 = Utc::now();
    let out = func(arg);
    let t1 = Utc::now();
    let dt = (t1 - t0).num_milliseconds();
    println!("{name}({arg}) = {out}, took {dt} ms");
}
