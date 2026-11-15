def ir_cu32_set_credit_v1 (bank : Nat -> Nat -> Nat) (owner address count : Nat) : Nat -> Nat -> Nat :=
fun (o a : Nat) => Bool.rec (fun (_ : Bool) => Nat) (bank o a) count (Bool.and (ir_nat_eqb owner o) (ir_nat_eqb address a))

inductive IRCU32HostV1 : Type
| mk : Nat -> (Nat -> Nat -> Nat) -> (Nat -> Nat) -> IRCU32HostV1

def ir_cu32_owner_v1 (host : IRCU32HostV1) : Nat := match host with
| IRCU32HostV1.mk owner credits alignment => owner

def ir_cu32_credit_v1 (host : IRCU32HostV1) (address : Nat) : Nat := match host with
| IRCU32HostV1.mk owner credits alignment => credits owner address

def ir_cu32_alignment_v1 (host : IRCU32HostV1) (address : Nat) : Nat := match host with
| IRCU32HostV1.mk owner credits alignment => alignment address

def ir_cu32_spend_v1 (host : IRCU32HostV1) (address : Nat) : IRCU32HostV1 := match host with
| IRCU32HostV1.mk owner credits alignment => IRCU32HostV1.mk owner (ir_cu32_set_credit_v1 credits owner address (Nat.sub (credits owner address) 1)) alignment

def ir_cu32_leaf_v1 (allocs : IRList IRByteAllocationV1) (address : Nat) : Bool :=
IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Bool) Bool.false
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Bool) =>
    Bool.or ih (Bool.and (ir_nat_eqb (ir_byte_alloc_base_v1 a) address)
      (Bool.and (ir_nat_eqb (ir_byte_alloc_size_v1 a) 12)
        (Bool.and (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_alloc_live_v1 a))))) allocs

def ir_cu32_heap_guard_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (address header : Nat) : Bool :=
Bool.and (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address 12 8)
  (Bool.and (ir_nat_eqb (ir_cu32_alignment_v1 host address) 8)
    (Bool.and (ir_cu32_leaf_v1 (ir_byte_mem_allocs_v1 mem) address)
      (Bool.and (ir_nat_eqb (Nat.div header 4294967296) 67108864)
        (ir_nat_ltb (Nat.mod header 4294967296) 4294967295))))

def ir_cu32_fault_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) : IRByteImportResultV1 IRCU32HostV1 :=
IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ub IRFault.bad_addr) mem host

def ir_cu32_return_v1 (value : IRScalar) (mem : IRByteMemoryV1) (host : IRCU32HostV1) : IRByteImportResultV1 IRCU32HostV1 :=
IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.cons IRScalar value (IRList.nil IRScalar))) mem host

def ir_cu32_decode_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (address : Nat) : IRByteImportResultV1 IRCU32HostV1 :=
Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
  (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address with
   | IROption.none => ir_cu32_fault_v1 mem host
   | IROption.some header => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
       (ir_cu32_fault_v1 mem host)
       (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
        | IROption.none => ir_cu32_fault_v1 mem host
        | IROption.some payload => ir_cu32_return_v1 (IRScalar.int_ payload) mem host)
       (ir_cu32_heap_guard_v1 mem host address header))
  (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
    (ir_cu32_fault_v1 mem host)
    (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host)
    (ir_nat_ltb (Nat.div address 2) 4294967296))
  (ir_nat_eqb (Nat.mod address 2) 1)

def ir_cu32_retire_leaf_v1 (address : Nat) (allocs : IRList IRByteAllocationV1) : IRList IRByteAllocationV1 :=
IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => IRList IRByteAllocationV1)
  (IRList.nil IRByteAllocationV1)
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (rest : IRList IRByteAllocationV1) =>
    IRList.cons IRByteAllocationV1
      (IRByteAllocationV1.mk (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a) (ir_byte_alloc_owner_v1 a)
        (Bool.and (ir_byte_alloc_live_v1 a) (Bool.not (ir_nat_eqb address (ir_byte_alloc_base_v1 a))))) rest) allocs

def ir_cu32_drop_memory_v1 (mem : IRByteMemoryV1) (address rc : Nat) : IRByteMemoryV1 :=
Bool.rec (fun (_ : Bool) => IRByteMemoryV1)
  (IRByteMemoryV1.mk
    (Bool.rec (fun (_ : Bool) => IRList IRByteAllocationV1) (ir_byte_mem_allocs_v1 mem)
      (ir_cu32_retire_leaf_v1 address (ir_byte_mem_allocs_v1 mem)) (ir_nat_eqb rc 0))
    (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) address 4
      (Bool.rec (fun (_ : Bool) => Nat) (Nat.sub rc 1) 4294967295 (ir_nat_eqb rc 0)))
    (ir_byte_mem_next_v1 mem))
  mem (ir_nat_leb 3758096384 rc)

def ir_cu32_release_heap_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (address : Nat) : IRByteImportResultV1 IRCU32HostV1 :=
match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address with
| IROption.none => ir_cu32_fault_v1 mem host
| IROption.some header => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
  (ir_cu32_fault_v1 mem host)
  (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
   | IROption.none => ir_cu32_fault_v1 mem host
   | IROption.some payload => IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar))
       (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address))
  (ir_cu32_heap_guard_v1 mem host address header)

def ir_cu32_release_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (address : Nat) : IRByteImportResultV1 IRCU32HostV1 :=
Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
  (ir_cu32_fault_v1 mem host)
  (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
    (ir_cu32_release_heap_v1 mem host address)
    (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
      (ir_cu32_fault_v1 mem host)
      (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) mem (ir_cu32_spend_v1 host address))
      (ir_nat_ltb (Nat.div address 2) 4294967296))
    (ir_nat_eqb (Nat.mod address 2) 1))
  (ir_nat_pos (ir_cu32_credit_v1 host address))

def ir_cu32_encode_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (value : Nat) : IRByteImportResultV1 IRCU32HostV1 :=
Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
  (ir_cu32_fault_v1 mem host)
  (ir_cu32_return_v1 (IRScalar.ptr_ (Nat.add (Nat.mul value 2) 1)) mem host)
  (ir_nat_ltb value 4294967296)

def ir_cu32_provider_v1 (decode encode release : Nat) : IRByteProvidersV1 IRCU32HostV1 :=
fun (fid : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : IRCU32HostV1) =>
match args with
| IRList.nil => ir_cu32_fault_v1 mem host
| IRList.cons value tail => match tail with
  | IRList.cons extra rest => ir_cu32_fault_v1 mem host
  | IRList.nil => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
      (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
        (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
          (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.unmodelled IRFault.width_bounded) mem host)
          (match value with
           | IRScalar.ptr_ address => ir_cu32_release_v1 mem host address
           | _ => ir_cu32_fault_v1 mem host) (ir_nat_eqb fid release))
        (match value with
         | IRScalar.int_ n => ir_cu32_encode_v1 mem host n
         | _ => ir_cu32_fault_v1 mem host) (ir_nat_eqb fid encode))
      (match value with
       | IRScalar.ptr_ address => ir_cu32_decode_v1 mem host address
       | _ => ir_cu32_fault_v1 mem host) (ir_nat_eqb fid decode)

def ir_cu32_decode_tagged_law_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (address : Nat)
  (tag : Eq Bool (ir_nat_eqb (Nat.mod address 2) 1) Bool.true) (fits : Eq Bool (ir_nat_ltb (Nat.div address 2) 4294967296) Bool.true) :
Eq (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_decode_v1 mem host address) (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host) :=
ir_byte_case_true_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_nat_eqb (Nat.mod address 2) 1) (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address with
   | IROption.none => ir_cu32_fault_v1 mem host
   | IROption.some header => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
       (ir_cu32_fault_v1 mem host)
       (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
        | IROption.none => ir_cu32_fault_v1 mem host
        | IROption.some payload => ir_cu32_return_v1 (IRScalar.int_ payload) mem host)
       (ir_cu32_heap_guard_v1 mem host address header)) (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
    (ir_cu32_fault_v1 mem host)
    (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host)
    (ir_nat_ltb (Nat.div address 2) 4294967296)) (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host) tag
  (ir_byte_case_true_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_nat_ltb (Nat.div address 2) 4294967296) (ir_cu32_fault_v1 mem host) (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host) (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host) fits (Eq.refl (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host)))

def ir_cu32_encode_law_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (value : Nat)
  (fits : Eq Bool (ir_nat_ltb value 4294967296) Bool.true) :
Eq (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_encode_v1 mem host value) (ir_cu32_return_v1 (IRScalar.ptr_ (Nat.add (Nat.mul value 2) 1)) mem host) :=
ir_byte_case_true_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_nat_ltb value 4294967296) (ir_cu32_fault_v1 mem host) (ir_cu32_return_v1 (IRScalar.ptr_ (Nat.add (Nat.mul value 2) 1)) mem host) (ir_cu32_return_v1 (IRScalar.ptr_ (Nat.add (Nat.mul value 2) 1)) mem host) fits (Eq.refl (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_return_v1 (IRScalar.ptr_ (Nat.add (Nat.mul value 2) 1)) mem host))

def ir_cu32_rc_write_frame_v1 (bytes : Nat -> IROption Nat) (address rc probe : Nat)
  (apart : Eq Bool (ir_byte_in_range_v1 address 4 probe) Bool.false) :
Eq (IROption Nat) (ir_byte_write_word_v1 bytes address 4 rc probe) (bytes probe) :=
ir_byte_write_outside_v1 bytes address 4 rc probe apart

def ir_cu32_case_false_v1 (A : Type) (guard : Bool) (no yes expected : A)
  (h : Eq Bool guard Bool.false) (step : Eq A no expected) :
Eq A (Bool.rec (fun (_ : Bool) => A) no yes guard) expected :=
Eq.subst Bool (fun (g : Bool) => Eq A (Bool.rec (fun (_ : Bool) => A) no yes g) expected)
  Bool.false guard (Eq.symm Bool guard Bool.false h) step

def ir_cu32_decode_heap_law_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (address header value : Nat)
  (notTag : Eq Bool (ir_nat_eqb (Nat.mod address 2) 1) Bool.false)
  (headerRead : Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address) (IROption.some Nat header))
  (valid : Eq Bool (ir_cu32_heap_guard_v1 mem host address header) Bool.true)
  (payloadRead : Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8)) (IROption.some Nat value)) :
Eq (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_decode_v1 mem host address) (ir_cu32_return_v1 (IRScalar.int_ value) mem host) :=
ir_cu32_case_false_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_nat_eqb (Nat.mod address 2) 1) (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address with
   | IROption.none => ir_cu32_fault_v1 mem host
   | IROption.some header => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
       (ir_cu32_fault_v1 mem host)
       (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
        | IROption.none => ir_cu32_fault_v1 mem host
        | IROption.some payload => ir_cu32_return_v1 (IRScalar.int_ payload) mem host)
       (ir_cu32_heap_guard_v1 mem host address header)) (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
    (ir_cu32_fault_v1 mem host)
    (ir_cu32_return_v1 (IRScalar.int_ (Nat.div address 2)) mem host)
    (ir_nat_ltb (Nat.div address 2) 4294967296)) (ir_cu32_return_v1 (IRScalar.int_ value) mem host) notTag
  (ir_byte_case_some_v1 Nat (IRByteImportResultV1 IRCU32HostV1) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address) header (ir_cu32_fault_v1 mem host)
    (fun (header : Nat) => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
       (ir_cu32_fault_v1 mem host)
       (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
        | IROption.none => ir_cu32_fault_v1 mem host
        | IROption.some payload => ir_cu32_return_v1 (IRScalar.int_ payload) mem host)
       (ir_cu32_heap_guard_v1 mem host address header)) (ir_cu32_return_v1 (IRScalar.int_ value) mem host) headerRead
    (ir_byte_case_true_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_heap_guard_v1 mem host address header) (ir_cu32_fault_v1 mem host) (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
        | IROption.none => ir_cu32_fault_v1 mem host
        | IROption.some payload => ir_cu32_return_v1 (IRScalar.int_ payload) mem host) (ir_cu32_return_v1 (IRScalar.int_ value) mem host) valid
      (ir_byte_case_some_v1 Nat (IRByteImportResultV1 IRCU32HostV1) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8)) value (ir_cu32_fault_v1 mem host)
        (fun (payload : Nat) => ir_cu32_return_v1 (IRScalar.int_ payload) mem host)
        (ir_cu32_return_v1 (IRScalar.int_ value) mem host) payloadRead (Eq.refl (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_return_v1 (IRScalar.int_ value) mem host)))))

def ir_cu32_release_heap_law_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (address header payload : Nat)
 (owned : Eq Bool (ir_nat_pos (ir_cu32_credit_v1 host address)) Bool.true) (notTag : Eq Bool (ir_nat_eqb (Nat.mod address 2) 1) Bool.false)
 (headerRead : Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address) (IROption.some Nat header))
 (valid : Eq Bool (ir_cu32_heap_guard_v1 mem host address header) Bool.true)
 (payloadRead : Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8)) (IROption.some Nat payload)) :
Eq (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_release_v1 mem host address) (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)) :=
ir_byte_case_true_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_nat_pos (ir_cu32_credit_v1 host address)) (ir_cu32_fault_v1 mem host) (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
    (ir_cu32_release_heap_v1 mem host address)
    (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
      (ir_cu32_fault_v1 mem host)
      (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) mem (ir_cu32_spend_v1 host address))
      (ir_nat_ltb (Nat.div address 2) 4294967296))
    (ir_nat_eqb (Nat.mod address 2) 1)) (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)) owned
 (ir_cu32_case_false_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_nat_eqb (Nat.mod address 2) 1) (ir_cu32_release_heap_v1 mem host address) (Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
      (ir_cu32_fault_v1 mem host)
      (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) mem (ir_cu32_spend_v1 host address))
      (ir_nat_ltb (Nat.div address 2) 4294967296)) (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)) notTag
  (ir_byte_case_some_v1 Nat (IRByteImportResultV1 IRCU32HostV1) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address) header (ir_cu32_fault_v1 mem host)
   (fun (header : Nat) => Bool.rec (fun (_ : Bool) => IRByteImportResultV1 IRCU32HostV1)
  (ir_cu32_fault_v1 mem host)
  (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
   | IROption.none => ir_cu32_fault_v1 mem host
   | IROption.some payload => IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar))
       (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address))
  (ir_cu32_heap_guard_v1 mem host address header)) (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)) headerRead
   (ir_byte_case_true_v1 (IRByteImportResultV1 IRCU32HostV1) (ir_cu32_heap_guard_v1 mem host address header) (ir_cu32_fault_v1 mem host) (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8) with
   | IROption.none => ir_cu32_fault_v1 mem host
   | IROption.some payload => IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar))
       (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)) (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)) valid
    (ir_byte_case_some_v1 Nat (IRByteImportResultV1 IRCU32HostV1) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 4 (Nat.add address 8)) payload (ir_cu32_fault_v1 mem host)
     (fun (payload : Nat) => (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address))) (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)) payloadRead (Eq.refl (IRByteImportResultV1 IRCU32HostV1) (IRByteImportResultV1.mk IRCU32HostV1 (IROutcome.ret (IRList.nil IRScalar)) (ir_cu32_drop_memory_v1 mem address (Nat.mod header 4294967296)) (ir_cu32_spend_v1 host address)))))))

def ir_cu32_credit_for_v1 (host : IRCU32HostV1) (owner address : Nat) : Nat := match host with
| IRCU32HostV1.mk current bank alignment => bank owner address

def ir_cu32_other_frame_credit_v1 (owner other address probe : Nat)
 (bank : Nat -> Nat -> Nat) (alignment : Nat -> Nat)
 (apart : Eq Bool (Bool.and (ir_nat_eqb owner other) (ir_nat_eqb address probe)) Bool.false) :
Eq Nat
 (ir_cu32_credit_for_v1 (ir_cu32_spend_v1 (IRCU32HostV1.mk owner bank alignment) address) other probe)
 (bank other probe) :=
ir_cu32_case_false_v1 Nat (Bool.and (ir_nat_eqb owner other) (ir_nat_eqb address probe))
 (bank other probe) (Nat.sub (bank owner address) 1) (bank other probe)
 apart (Eq.refl Nat (bank other probe))

def ir_cu32_allocation_at_v1 (allocs : IRList IRByteAllocationV1) (address : Nat) : IROption IRByteAllocationV1 :=
IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => IROption IRByteAllocationV1)
 (IROption.none IRByteAllocationV1)
 (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (rest : IROption IRByteAllocationV1) =>
  Bool.rec (fun (_ : Bool) => IROption IRByteAllocationV1) rest (IROption.some IRByteAllocationV1 a)
   (ir_nat_eqb (ir_byte_alloc_base_v1 a) address)) allocs

def ir_cu32_tagged_roundtrip_v1 (value : Nat) :
Eq Nat (Nat.div (Nat.add (Nat.mul value 2) 1) 2) value :=
ir_byte_div_unique_v1 (Nat.add (Nat.mul value 2) 1) 2 value 1
 (@Nat.zero_lt_succ 1) (@Nat.le_refl 2)
 (Eq.refl Nat (Nat.add (Nat.mul value 2) 1))

def ir_cu32_live_weaken_v1 (live hit okay : Bool)
 (h : Eq Bool (Bool.or (Bool.not live) okay) Bool.true) :
Eq Bool (Bool.or (Bool.not (Bool.and live (Bool.not hit))) okay) Bool.true :=
Bool.rec (fun (l : Bool) => Eq Bool (Bool.or (Bool.not l) okay) Bool.true ->
 Eq Bool (Bool.or (Bool.not (Bool.and l (Bool.not hit))) okay) Bool.true)
 (fun (old : Eq Bool (Bool.or (Bool.not Bool.false) okay) Bool.true) => Eq.refl Bool Bool.true)
 (fun (old : Eq Bool (Bool.or (Bool.not Bool.true) okay) Bool.true) =>
  Bool.rec (fun (b : Bool) => Eq Bool (Bool.or (Bool.not (Bool.and Bool.true (Bool.not b))) okay) Bool.true)
   old (Eq.refl Bool Bool.true) hit) live h

def ir_cu32_retire_preserves_owners_v1 (mem : IRByteMemoryV1) (address : Nat) (owners : IRList Nat) (next : Nat)
 (before : Eq Bool (ir_byte_memory_owners_v1 mem owners next) Bool.true) :
Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk (ir_cu32_retire_leaf_v1 address (ir_byte_mem_allocs_v1 mem)) (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) Bool.true :=
IRList.rec IRByteAllocationV1 (fun (xs : IRList IRByteAllocationV1) => Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk xs (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) Bool.true -> Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk (ir_cu32_retire_leaf_v1 address xs) (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) Bool.true)
 (fun (_ : Eq Bool Bool.true Bool.true) => Eq.refl Bool Bool.true)
 (fun (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
  (ih : Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) Bool.true -> Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk (ir_cu32_retire_leaf_v1 address tail) (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) Bool.true) =>
  fun (h : Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk (IRList.cons IRByteAllocationV1 a tail) (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) Bool.true) => (ir_byte_world_and_intro_v1 (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk (ir_cu32_retire_leaf_v1 address tail) (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) (Bool.and (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (Bool.and (ir_byte_alloc_live_v1 a) (Bool.not (ir_nat_eqb address (ir_byte_alloc_base_v1 a))))) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))))) (ih (ir_byte_world_and_left_v1 (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) (Bool.and (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))))) h)) (ir_byte_world_and_intro_v1 (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (Bool.and (ir_byte_alloc_live_v1 a) (Bool.not (ir_nat_eqb address (ir_byte_alloc_base_v1 a))))) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners)))) (ir_byte_world_and_left_v1 (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners)))) (ir_byte_world_and_right_v1 (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) (Bool.and (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))))) h)) (ir_byte_world_and_intro_v1 (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (Bool.and (ir_byte_alloc_live_v1 a) (Bool.not (ir_nat_eqb address (ir_byte_alloc_base_v1 a))))) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))) (ir_byte_world_and_left_v1 (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))) (ir_byte_world_and_right_v1 (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners)))) (ir_byte_world_and_right_v1 (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) (Bool.and (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))))) h))) (ir_cu32_live_weaken_v1 (ir_byte_alloc_live_v1 a) (ir_nat_eqb address (ir_byte_alloc_base_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners)) (ir_byte_world_and_right_v1 (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))) (ir_byte_world_and_right_v1 (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners)))) (ir_byte_world_and_right_v1 (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) owners next) (Bool.and (ir_byte_alloc_valid_v1 a) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 a)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners))))) h))))))))
 (ir_byte_mem_allocs_v1 mem) before

def ir_cu32_drop_preserves_owners_v1 (mem : IRByteMemoryV1) (address rc : Nat) (owners : IRList Nat) (next : Nat)
 (before : Eq Bool (ir_byte_memory_owners_v1 mem owners next) Bool.true) :
Eq Bool (ir_byte_memory_owners_v1 (ir_cu32_drop_memory_v1 mem address rc) owners next) Bool.true :=
Bool.rec (fun (b : Bool) => Eq Bool (ir_byte_memory_owners_v1
 (Bool.rec (fun (_ : Bool) => IRByteMemoryV1) (IRByteMemoryV1.mk (Bool.rec (fun (_ : Bool) => IRList IRByteAllocationV1) (ir_byte_mem_allocs_v1 mem) (ir_cu32_retire_leaf_v1 address (ir_byte_mem_allocs_v1 mem)) (ir_nat_eqb rc 0)) (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) address 4 (Bool.rec (fun (_ : Bool) => Nat) (Nat.sub rc 1) 4294967295 (ir_nat_eqb rc 0))) (ir_byte_mem_next_v1 mem)) mem b) owners next) Bool.true)
 (Bool.rec (fun (b : Bool) => Eq Bool (ir_byte_memory_owners_v1
 (IRByteMemoryV1.mk (Bool.rec (fun (_ : Bool) => IRList IRByteAllocationV1) (ir_byte_mem_allocs_v1 mem) (ir_cu32_retire_leaf_v1 address (ir_byte_mem_allocs_v1 mem)) b) (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) address 4 (Bool.rec (fun (_ : Bool) => Nat) (Nat.sub rc 1) 4294967295 (ir_nat_eqb rc 0))) (ir_byte_mem_next_v1 mem)) owners next) Bool.true)
 before (ir_cu32_retire_preserves_owners_v1 mem address owners next before) (ir_nat_eqb rc 0)) before (ir_nat_leb 3758096384 rc)

def ir_cu32_total_credit_v1 (host : IRCU32HostV1) (owners : IRList Nat) (address : Nat) : Nat :=
IRList.rec Nat (fun (_ : IRList Nat) => Nat) 0
 (fun (owner : Nat) (_ : IRList Nat) (rest : Nat) => Nat.add (ir_cu32_credit_for_v1 host owner address) rest) owners

def ir_cu32_owned_guard_v1 (mem : IRByteMemoryV1) (host : IRCU32HostV1) (owners : IRList Nat) (address : Nat) : Bool :=
let total : Nat := ir_cu32_total_credit_v1 host owners address;
Bool.rec (fun (_ : Bool) => Bool)
 (Bool.rec (fun (_ : Bool) => Bool)
  (match ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 address with
   | IROption.none => Bool.false
   | IROption.some header => Bool.and (ir_cu32_heap_guard_v1 mem host address header)
      (Bool.or (ir_nat_leb 3758096384 (Nat.mod header 4294967296))
       (ir_nat_leb total (Nat.add (Nat.mod header 4294967296) 1))))
  (ir_nat_ltb (Nat.div address 2) 4294967296)
  (ir_nat_eqb (Nat.mod address 2) 1))
 Bool.true (ir_nat_eqb total 0)
