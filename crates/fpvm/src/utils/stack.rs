//! This module contains utillities for tracking program stacks.

use crate::{types::Address, utils::meta::Meta};

pub(crate) struct Stack {
    rep: Vec<Address>,
    caller: Vec<Address>,
    meta: Meta,
}

impl Stack {
    pub fn new(meta: Meta) -> Stack {
        Stack { rep: Vec::new(), caller: Vec::new(), meta }
    }

    pub fn push(&mut self, pc: Address, target: Address) {
        self.rep.push(target);
        self.caller.push(pc);
    }

    pub fn pop(&mut self, pc: Address) {
        if let Some(last) = self.rep.last() {
            let func = self.meta.lookup(pc);
            let top_func = self.meta.lookup(*last);
            if func != top_func {
                // handle inlining by searching for a likely return
                let idx = self.rep.len() - 1;
                for i in (0..=idx).rev() {
                    if self.meta.lookup(self.rep[i]) == func {
                        self.rep.truncate(i);
                        self.caller.truncate(i);
                        break;
                    }
                }
            } else {
                self.rep.pop();
                self.caller.pop();
            }
        } else {
            //println!("error: stack overflow. target={:?}", target);
            return;
        }
    }

    #[allow(dead_code)]
    pub fn traceback<F>(&self, mut f: F)
    where
        F: FnMut(Address, Address),
    {
        for i in (0..=self.rep.len() - 1).rev() {
            f(self.rep[i], self.caller[i]);
        }
    }
}
