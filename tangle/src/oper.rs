const HOST_WIDTH: u8 = std::mem::size_of::<usize>() as u8;
const STACK_TOP: usize = 0xFFFF_FFFF_FFFF_FFF0;
const STACK: RegSpec = RegSpec::rsp();

    pub fn check_cond(&mut self, cond: IntCC) -> JitValue {
        let flags = match cond {
            IntCC::UnsignedGreaterThan => {
                vec![Flags::CF, Flags::ZF]
            },
            IntCC::UnsignedGreaterThanOrEqual => {
                vec![Flags::CF]
            },
            IntCC::UnsignedLessThan => {
                vec![Flags::CF]
            },
            IntCC::UnsignedLessThanOrEqual => {
                vec![Flags::CF, Flags::ZF]
            },
            IntCC::Equal => {
                vec![Flags::ZF]
            },
            IntCC::NotEqual => {
                vec![Flags::ZF]
            },
            _ => unimplemented!("unimplemented check_cond for {}", cond),
        };
        let mut val = None;
        let mut same = true;
        for flag in flags {
            let flag_cond = &self.context.flags[flag as usize];
            if let Some(set_val) = val {
                if set_val != flag_cond {
                    same = false;
                    break;
                }
            } else {
                val = Some(flag_cond);
            }
        }
        if !same {
            unimplemented!();
        }
        if let Some(JitFlag::Unknown(left, right, res)) = val {
            JitValue::Flag(self.builder.ins().ifcmp(*left, *right))
        } else if let Some(JitFlag::Known(c)) = val {
            println!("constant eflags {:?} with cond {}", c, cond);
            let tmp = match cond {
                IntCC::UnsignedGreaterThan => {
                    // CF=0 and ZF=0
                    let cf = self.context.check_flag(Flags::CF, false, self.builder);
                    let zf = self.context.check_flag(Flags::ZF, false, self.builder);
                    self.band(cf, zf)
                },
                IntCC::UnsignedGreaterThanOrEqual => {
                    // CF=0
                    self.context.check_flag(Flags::CF, false, self.builder)
                },
                IntCC::UnsignedLessThan => {
                    // CF=1
                    self.context.check_flag(Flags::CF, true, self.builder)
                },
                IntCC::UnsignedLessThanOrEqual => {
                    // CF=1 or ZF=1
                    let cf = self.context.check_flag(Flags::CF, true, self.builder);
                    let zf = self.context.check_flag(Flags::ZF, true, self.builder);
                    self.bor(cf, zf)
                },
                IntCC::Equal => {
                    self.context.check_flag(Flags::ZF, true, self.builder)
                },
                IntCC::NotEqual => {
                    self.context.check_flag(Flags::ZF, false, self.builder)
                }
                _ => unimplemented!(),
            };
            // XXX: does cranelift do something dumb and actually make this clobber
            // an entire register or something?
            tmp.zero_extend(self.builder, HOST_WIDTH).into_native(self.builder).unwrap()
        } else {
            unimplemented!()
        }
    }


    /// Get left+right for JitValues.
    /// if FLAG is true, then self.context.flags are updated with eflags
    pub fn add<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left, right) {
            (Value(val_left, typ_left), Value(val_right, _)) => {
                let (res, flag) = self.builder.ins().iadd_cout(val_left, val_right);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (left @ _ , right @ Value(_, _))
            | (left @ Value(_, _), right @ _) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let (res, flag) = self.builder.ins().iadd_cout(_left, _right);
                self.context.set_flags(flags, (_left, _right, res));
                Value(res, typ)
            },
            (Ref(base, offset), c) if c.is_const() => {
                let c = c.into_usize(self.builder).unwrap();
                Ref(base, do_op!(self.context, FLAG, offset, (c), "add {}, {}", flags, +))
            },
            (offset, Ref(base, c)) if offset.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                Ref(base, do_op!(self.context, FLAG, offset, (c), "add {}, {}", flags, +))
            },
            (left_c, mut right_c) if left_c.clone().is_const() && right_c.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                const_ops!(self.context, FLAG, left_c.clone(), (right_c.clone()), "add {}, {}", flags, +)
            },
            (left, right) => unimplemented!("unimplemented add {:?} {:?}", left, right)
        }
    }

    /// Add with carry
    pub fn adc<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp, carry: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left.clone(), right.clone(), carry.clone()) {
            (Value(val_left, typ_left), Value(val_right, _), Flag(val_carry)) => {
                let (res, flag) = self.builder.ins().iadd_carry(val_left, val_right, val_carry);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (_, _, carry) if carry.is_const() => {
                // basically, this sucks a lot:
                // iadd_carry is broken on cranelift (#2860), so we work around
                // it by lowering to a normal iadd_cout in the CF=false case,
                // and to two iadd_cout's in the CF=true case (and then have to
                // fixup our carry flag so the spliced +1 doesn't break).
                let carry = carry.into_usize(self.builder).unwrap();
                if carry == 0 {
                    return self.add::<FLAG>(left, right);
                } else {
                    let left_plus_one = self.add::<FLAG>(left, Const8(1));
                    // track if the +1 overflowed
                    let carried = self.context.check_flag(Flags::CF, true, self.builder);

                    let res = self.add::<FLAG>(left_plus_one, right);
                    if(FLAG) {
                        // if the +1 definitely carried, we know that carry has to
                        // be set.
                        println!("carried = {:?}", carried);
                        if let JitTemp::Const64(1) = carried {
                            self.context.flags[Flags::CF as usize] = JitFlag::Known(1 << Flags::CF as usize);
                        } else if let JitTemp::Const64(0) = carried {
                            ();
                        } else if let JitTemp::Value(val, typ) = carried {
                            unimplemented!("double check this");
                            // but if we don't know, then we have to OR it with
                            // the other carry flag (which sucks!)
                            let other_carried = self.context.check_flag(Flags::CF, true, self.builder);
                            let maybe_carried = self.bor(other_carried, carried);
                            self.context.set_flags(vec![Flags::CF],
                                (left_plus_one.into_ssa(typ, self.builder),
                                 right.into_ssa(typ, self.builder),
                                 maybe_carried.into_ssa(typ, self.builder)));
                        } else {
                            unimplemented!();
                        }
                    }
                    return res;
                }
            },
            (left @ Value(_, _), right @ _, carry @ _) |
            (left @ _, right @ Value(_, _), carry @ _) |
            (left @ _, right @ _, carry @ Flag(_)) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let mut _carry = carry.into_ssa(types::IFLAGS, self.builder);
                let (res, flag) = self.builder.ins().iadd_ifcarry(_left, _right, _carry);
                self.context.set_flags(flags, (_left, _right, flag));
                Value(res, typ)
            },
            (Ref(base, offset), off, carry) if off.is_const() && carry.is_const() => {
                let off = off.into_usize(self.builder).unwrap();
                let carry = carry.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if carry == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "add {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; adc {}, {}", flags, +))
                }
            },
            (offset, Ref(base, off), carry) if offset.is_const() && carry.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                let carry = carry.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if carry == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "add {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; adc {}, {}", flags, +))
                }
            },
            (left_c, mut right_c, mut carry_c)
            if left_c.clone().is_const()
            && right_c.clone().is_const()
            && carry_c.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                let carry_c = carry_c.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if carry_c == 0 {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "add {}, {}", flags, +)
                } else {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "stc; adc {}, {}", flags, +)
                }
            },
            (left, right, carry) => unimplemented!("unimplemented adc {:?} {:?} {:?}", left, right, carry)
        }
    }



    pub fn sub<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left, right) {
            // sub dest, val is always a dest sized output
            (Value(val_left, typ_left), Value(val_right, _)) => {
                let (res, flag) = self.builder.ins().isub_ifbout(val_left, val_right);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (left @ _ , right @ Value(_, _))
            | (left @ Value(_, _), right @ _) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let (res, flag) = self.builder.ins().isub_ifbout(_left, _right);
                self.context.set_flags(flags, (_left, _right, flag));
                Value(res, typ)
            },
            // XXX: this is technically incorrect: flags will be wrong, because
            // it's actually supposed to be the flags for (base+offset) - c.
            // let's just miscompile for now? not sure how common cmp reg, c
            // to test pointer equality would be.
            (Ref(base, offset), c) if c.is_const() => {
                let c = c.into_usize(self.builder).unwrap();
                assert!(c < offset && c < 0x100);
                Ref(base, do_op!(self.context, FLAG, offset, c, "sub {}, {}", flags, -))
            },
            (offset, Ref(base, c)) if offset.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                assert!(c < offset && c < 0x100);
                Ref(base, do_op!(self.context, FLAG, offset, c, "sub {}, {}", flags, -))
            },
            (left_c, mut right_c) if left_c.clone().is_const() && right_c.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "sub {}, {}", flags, -)
            },
            (left, right) => unimplemented!("unimplemented sub {:?} {:?}", left, right)
        }
    }

    /// Sub with borrow
    pub fn sbb<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp, borrow: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left.clone(), right.clone(), borrow.clone()) {
            (Value(val_left, typ_left), Value(val_right, _), Flag(val_borrow)) => {
                let (res, flag) = self.builder.ins().isub_borrow(val_left, val_right, val_borrow);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (_, _, borrow) if borrow.is_const() => {
                // see note in self.adc
                let borrow = borrow.into_usize(self.builder).unwrap();
                if borrow == 0 {
                    return self.sub::<FLAG>(left, right);
                } else {
                    unimplemented!()
                }
            },
            (left @ Value(_, _), right @ _, borrow @ _) |
            (left @ _, right @ Value(_, _), borrow @ _) |
            (left @ _, right @ _, borrow @ Flag(_)) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let mut _borrow = borrow.into_ssa(types::IFLAGS, self.builder);
                let (res, flag) = self.builder.ins().isub_borrow(_left, _right, _borrow);
                self.context.set_flags(flags, (_left, _right, flag));
                Value(res, typ)
            },
            (Ref(base, offset), off, borrow) if off.is_const() && borrow.is_const() => {
                let off = off.into_usize(self.builder).unwrap();
                let borrow = borrow.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if borrow == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "sub {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; sbb {}, {}", flags, +))
                }
            },
            (offset, Ref(base, off), borrow) if offset.is_const() && borrow.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                let borrow = borrow.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if borrow == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "sub {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; sbb {}, {}", flags, +))
                }
            },
            (left_c, mut right_c, mut borrow)
            if left_c.clone().is_const()
            && right_c.clone().is_const()
            && borrow.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                let borrow = borrow.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if borrow == 0 {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "sub {}, {}", flags, +)
                } else {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "stc; sbb {}, {}", flags, +)
                }
            },
            (left, right, borrow) => unimplemented!("unimplemented sbb {:?} {:?} {:?}", left, right, borrow)
        }
    }



    pub fn band(&mut self, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        let biggest = max(left.width(), right.width());
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // XXX: set flags!!
        match (left.clone(), right.clone()) {
            (c, other) | (other, c) if c.is_const() => {
                let fixed_c = c.into_usize(self.builder).unwrap();
                match (fixed_c, other.clone()) {
                    //0 & val or val & 0 = 0
                    (0, _) => return JitTemp::val_of_width(0, biggest),
                    // !0 & val or val & !0 = val
                    (const { !0 as usize }, _) => return other,
                    // left_c & right_c is just left & right
                    (fixed_c, other) if other.clone().is_const() => {
                        let fixed_other = other.into_usize(self.builder).unwrap();
                        return JitTemp::val_of_width(fixed_c & fixed_other, biggest)
                    },
                    (_, _) => (),
                }
            },
            _ => (),
        };

        match (left, right) {
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left, typ_left), Value(val_right, typ_right)) => {
                Value(self.builder.ins().band(val_left, val_right), typ_left)
            },
            (val @ _, Value(ssa, ssa_typ))
            | (Value(ssa, ssa_typ), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().band(ssa_val, ssa), ssa_typ)
            },
            (Ref(base, offset), _)
            | (_, Ref(base, offset)) => {
                unimplemented!("band pointer")
            },
            (left, right) => unimplemented!("unimplemented band {:?} {:?}", left, right)
        }
    }

    pub fn bor(&mut self, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        let biggest = max(left.width(), right.width());
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // XXX: set flags!!
        match (left.clone(), right.clone()) {
            (c, other) | (other, c) if c.is_const() => {
                let fixed_c = c.into_usize(self.builder).unwrap();
                match (fixed_c, other) {
                    //0 | val or val | 0 = 0
                    (0, val) => return val,
                    // left_c | right_c is just left | right
                    (fixed_c, other) if other.is_const() => {
                        let fixed_other = other.into_usize(self.builder).unwrap();
                        return JitTemp::val_of_width(fixed_c | fixed_other, biggest)
                    },
                    (_, _) => (),
                }
            },
            _ => (),
        };

        match (left, right) {
            (Value(val_left, typ_left), Value(val_right, typ_right)) => {
                Value(self.builder.ins().bor(val_left, val_right), typ_left)
            },
            (val @ _, Value(ssa, ssa_typ))
            | (Value(ssa, ssa_typ), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bor(ssa_val, ssa), ssa_typ)
            },
            (Ref(base, offset), _)
            | (_, Ref(base, offset)) => {
                unimplemented!("bor pointer")
            },
            (left, right) => unimplemented!("unimplemented bor {:?} {:?}", left, right)
        }
    }

    pub fn bxor(&mut self, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        if left == right {
            return JitTemp::val_of_width(0, left.width())
        }
        let biggest = max(left.width(), right.width());
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // XXX: set flags
        match (left.clone(), right.clone()) {
            (c, other) | (other, c) if c.is_const() => {
                let fixed_c = c.into_usize(self.builder).unwrap();
                match (fixed_c, other) {
                    (fixed_c, other) if other.is_const() => {
                        let fixed_other = other.into_usize(self.builder).unwrap();
                        return JitTemp::val_of_width(fixed_c ^ fixed_other, biggest)
                    },
                    (_, _) => (),
                }
            },
            _ => (),
        }

        match (left, right) {
            (Value(val_left, typ_left), Value(val_right, typ_right)) => {
                Value(self.builder.ins().bxor(val_left, val_right), typ_left)
            },
            (val @ _, Value(ssa, ssa_typ))
            | (Value(ssa, ssa_typ), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bxor(ssa_val, ssa), ssa_typ)
            },
            (left, right) => unimplemented!("unimplemented bxor {:?} {:?}", left, right)
        }
    }

    pub fn bitselect(&mut self, mut control: JitTemp, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        let biggest = max(control.width(), max(left.width(), right.width()));
        println!("bitselect {:?} {:?} {:?} (biggest={})", control, left, right, biggest);
        control = control.zero_extend(self.builder, biggest);
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // bitselect doesn't have a set flags version
        if control.is_const() {
            let fixed_control = control.clone().into_usize(self.builder).unwrap();
            match fixed_control {
                //bitselect(0, left, right) => right
                0 => return right,
                //bitselect(!0, left, right) => left
                const { !0 as usize } => return left,
                _ => (),
            };
        }
        if left.is_const() {
            let fixed_left = left.clone().into_usize(self.builder).unwrap();
            match fixed_left {
                //bitselect(control, 0, right) => !control & right
                0 => {
                    let ncontrol = self.bnot(control);
                    return self.band(ncontrol, right)
                },
                _ => ()
            };
        }
        if right.is_const() {
            let fixed_right = right.clone().into_usize(self.builder).unwrap();
            match fixed_right {
                //bitselect(control, left, 0) => control & left
                0 => return self.band(control, left),
                _ => ()
            }
        }
        match (control, left, right) {
            (control, left, right) if control.is_const() && left.is_const() && right.is_const() => {
                let true_mask = self.band(control.clone(), left);
                let not_control = self.bnot(control);
                let false_mask = self.band(not_control, right);
                self.bor(true_mask, false_mask)
            },
            (control @ _, Value(val_left, typ_left), Value(val_right, _)) => {
                let control = control.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bitselect(control, val_left, val_right), typ_left)
            },
            (control, left, right) =>
                unimplemented!("unimplemented bitselect {:?} {:?} {:?}", control, left, right)

        }
    }

    pub fn bnot(&mut self, val: JitTemp) -> JitTemp {
        use JitTemp::*;
        match val {
            Value(val, typ) => Value(self.builder.ins().bnot(val), typ),
            Const8(c) => Const8(!c),
            Const16(c) => Const16(!c),
            Const32(c) => Const32(!c),
            Const64(c) => Const64(!c),
            _ => unimplemented!("bnot {:?}", val),
        }
    }

