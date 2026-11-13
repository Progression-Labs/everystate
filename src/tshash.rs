//! The TypeScript engine's state fingerprint (two 32-bit murmur-style streams), reproduced bit for bit.
//! Only used for node identifiers in `-dump dot` output, so that dumps are identical to the reference.
use crate::checker::Checker;
use crate::eval::StateRef;
use crate::intern::*;
use crate::value::*;

struct H {
    h1: i32,
    h2: i32,
}
fn imul(a: i32, b: i32) -> i32 {
    a.wrapping_mul(b)
}
impl H {
    fn add(&mut self, x: i32) {
        let mut k = imul(x, 0xcc9e2d51u32 as i32);
        k = k.rotate_left(15);
        k = imul(k, 0x1b873593);
        let mut h = self.h1 ^ k;
        h = h.rotate_left(13);
        self.h1 = imul(h, 5).wrapping_add(0xe6546b64u32 as i32);
        k = imul(x ^ 0x5bd1e995, 0x85ebca6bu32 as i32);
        k = k.rotate_left(13);
        k = imul(k, 0xc2b2ae35u32 as i32);
        h = self.h2 ^ k;
        h = h.rotate_left(17);
        self.h2 = imul(h, 5).wrapping_add(0x52dce729);
    }
    fn value(&mut self, v: &Value) -> R<()> {
        match v {
            Value::Int(i) => {
                self.add(1);
                self.add(*i as i32);
                if *i > 0x7fffffff || *i < -0x80000000 {
                    self.add((*i as f64 / 4294967296.0) as i32);
                }
            }
            Value::Bool(b) => self.add(if *b { 3 } else { 2 }),
            Value::Str(s) => {
                self.add(4);
                self.add(s.0 as i32 + 1);
            }
            Value::Tuple(t) => {
                self.add(5);
                self.add(t.len() as i32);
                for x in t.iter() {
                    self.value(x)?;
                }
            }
            Value::Record(r) => {
                self.add(6);
                self.add(r.names.len() as i32);
                for i in 0..r.names.len() {
                    self.add(r.names[i].0 as i32 + 1);
                    self.value(&r.vals[i])?;
                }
            }
            Value::Set(s) => {
                let e = s.elems()?;
                self.add(7);
                self.add(e.len() as i32);
                for x in e {
                    self.value(x)?;
                }
            }
            Value::Fcn(f) => {
                self.add(8);
                self.add(f.dom.len() as i32);
                for i in 0..f.dom.len() {
                    self.value(&f.dom[i])?;
                    self.value(&f.vals[i])?;
                }
            }
            Value::Model(m) => {
                self.add(9);
                self.add(m.0 as i32 + 1);
            }
            _ => return eval_err("Attempted to fingerprint a non-value (operator or lazy function).".into()),
        }
        Ok(())
    }
    fn finish(&mut self) {
        let mut h = self.h1 as u32;
        h ^= h >> 16;
        h = h.wrapping_mul(0x85ebca6b);
        h ^= h >> 13;
        h = h.wrapping_mul(0xc2b2ae35);
        h ^= h >> 16;
        self.h1 = h as i32;
        let mut h = (self.h2 ^ self.h1) as u32;
        h ^= h >> 15;
        h = h.wrapping_mul(0x2c1b3c6d);
        h ^= h >> 12;
        h = h.wrapping_mul(0x297a2d39);
        h ^= h >> 15;
        self.h2 = h as i32;
    }
}

pub fn fingerprint(c: &Checker, s: &StateRef) -> R<i64> {
    let mut h = H { h1: 0x9747b28cu32 as i32, h2: 0x3c6ef372 };
    for v in c.fingerprint_input(s)? {
        h.value(&v)?;
    }
    h.finish();
    Ok((((h.h1 as u32 as u64) << 32) | (h.h2 as u32 as u64)) as i64)
}
