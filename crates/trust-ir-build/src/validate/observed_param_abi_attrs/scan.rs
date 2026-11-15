// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            work.admit(1, size_of::<usize>())?;
            if let Some(signature) = work.at(&module.func_types, function.ty.as_usize())? {
                work.admit(1, size_of::<bool>())?;
                let mut sret_seen = false;
                let mut index = 0;
                while let Some(pa) = work.at(&function.attrs.params, index)? {
                    work.admit(2, 2 * size_of::<bool>())?;
                    if pa.byval || pa.sret {
                        if let Some(ty) = work.at(&signature.params, index)? {
                            work.admit(1, 0)?;
                            if pa.byval && pa.sret {
                                self.issue(
                                    function,
                                    index,
                                    "byval and sret are mutually exclusive on one parameter",
                                    work,
                                )?;
                            }
                            work.admit(1, 0)?;
                            if !matches!(
                                ty,
                                Ty::Ptr
                                    | Ty::PtrConst(_)
                                    | Ty::PtrMut(_)
                                    | Ty::Ref(_)
                                    | Ty::RefMut(_)
                            ) {
                                self.issue(
                                    function,
                                    index,
                                    "byval/sret require a pointer-typed parameter",
                                    work,
                                )?;
                            }
                            work.admit(1, 0)?;
                            if pa.sret {
                                work.admit(1, 0)?;
                                if sret_seen {
                                    self.issue(
                                        function,
                                        index,
                                        "at most one parameter may be sret",
                                        work,
                                    )?;
                                }
                                work.admit(2, size_of::<bool>())?;
                                sret_seen = true;
                                if !signature.returns.is_empty() {
                                    self.issue(function,index,"sret marks the return slot, so the signature must return no values",work)?;
                                }
                            }
                        } else {
                            self.issue(
                                function,
                                index,
                                "attribute is positioned past the signature's parameters",
                                work,
                            )?;
                        }
                    }
                    work.next(&mut index)?;
                }
            }
            work.next(&mut f)?;
        }
        Ok(())
    }
}
