// Motivation: How to use unsafe interior mutability
// See https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html

use std::cell::UnsafeCell;
use std::ops::Deref;
use std::pin::Pin;

struct HasMutFields {
    value1: UnsafeCell<i64>,
    value2: Pin<Box<i64>>,
    // Points to value2's data. Same as *const i64 but easier to access
    to_value2: &'static UnsafeCell<i64>,
}

#[derive(Copy, Clone)]
enum MutField {
    V1,
    V2,
}

impl HasMutFields {
    unsafe fn new() -> Self {
        let value1 = UnsafeCell::new(0);
        let value2 = Box::pin(0);
        // Cast from &i64 to *i64 to *UnsafeCell<i64>
        let ptr_to_value_2 = value2.deref() as *const i64 as *const UnsafeCell<i64>;
        // Finally cast to &UnsafeCell<i64> for easier access
        let to_value2 = &*ptr_to_value_2;
        Self {
            value1,
            value2,
            to_value2,
        }
    }

    unsafe fn set(&self, value: i64, to: MutField) {
        match to {
            MutField::V1 => {
                *self.value1.get() = value
            }
            MutField::V2 => {
                *self.to_value2.get() = value
            }
        }
    }

    unsafe fn repr(&self) -> String {
        let v1 = *self.value1.get();
        let v2 = *self.value2;
        let v2_alt = *self.to_value2.get();
        format!("v1 = {v1}, v2 = {v2}, v2_alt = {v2_alt}")
    }

    // Make sure writes to UnsafeCell alias all reads
    unsafe fn mutate_and_repr(&self, new_v2: i64) -> String {
        let v2 = *self.value2;
        let v2_alt = *self.to_value2.get();
        *self.to_value2.get() = new_v2;
        let changed_v2 = *self.value2;
        let changed_v2_alt = *self.to_value2.get();
        format!("Before: {v2}, alt = {v2_alt}; After: {changed_v2}, alt = {changed_v2_alt}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_mut() {
        unsafe {
            let target = HasMutFields::new();
            println!("Init = {}", target.repr());
            target.set(1, MutField::V1);
            target.set(2, MutField::V2);
            println!("After set = {}", target.repr());
            println!("After set = {}", target.mutate_and_repr(42));
        }
    }
}
