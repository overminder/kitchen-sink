use std::ffi::{c_char, CString};

extern {
    fn fibo_asm_internal(n: i64) -> i64;
    fn get1() -> i64;
    fn fiboInterp(n: i64, which: *const c_char) -> i64;
}

pub fn fibo_asm(n: i64) -> i64 {
    unsafe {
        fibo_asm_internal(n)
    }
}

pub fn fibo_interp_fast(n: i64) -> i64 {
    unsafe {
        let cstr = CString::new("fast").unwrap();
        fiboInterp(n, cstr.as_ptr())
    }
}

pub fn fibo_interp_slow(n: i64) -> i64 {
    unsafe {
        let cstr = CString::new("slow").unwrap();
        fiboInterp(n, cstr.as_ptr())
    }
}

pub fn fibo_rs(n: i64) -> i64 {
    if n < 2 {
        n
    } else {
        fibo_rs(n - 1) + fibo_rs(n - 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get1_works() {
        let result = unsafe { get1() };
        assert_eq!(result, 1);
    }

    #[test]
    fn fibo_asm_works() {
        let result = fibo_asm(10);
        assert_eq!(result, 55);
    }
}
