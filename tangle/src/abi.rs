use crate::region::Region;
use crate::port::Storage;
use yaxpeax_x86::long_mode::RegSpec;

use core::fmt::Debug;

pub trait Abi: Debug {
    fn constrain_arguments(&self, reg: &mut Region);
    fn constrain_returns(&self, reg: &mut Region);
}

#[derive(Default, Clone, Debug)]
pub struct x86_64;

impl Abi for x86_64 {
    fn constrain_arguments(&self, reg: &mut Region) {
        let arg_map = vec![
            RegSpec::rdi(),
            RegSpec::rsi(),
            RegSpec::rdx(),
        ];
        for (i, arg) in reg.sources.clone().iter().enumerate() {
            reg.constrain(*arg, Storage::Physical(arg_map[i as usize].clone()));
        }
    }

    fn constrain_returns(&self, reg: &mut Region) {
        let out_map = vec![
            RegSpec::rax(),
            RegSpec::rdx(),
        ];
        for (i, arg) in reg.sinks.clone().iter().enumerate() {
            reg.constrain(*arg, Storage::Physical(out_map[i as usize].clone()));
        }
    }
}
