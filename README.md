# Lineiform

Lineiform is a meta-JIT library for Rust interpreters. Given an interpreter that uses closure generation, it allows an author to add minimal annotations and calls into Lineiform in order to automagically get an optimizing method JIT, via runtime function inlining and constant propagation to resolve dynamic calls to closed environment members. Internally it does lifting of closure bodies from x86 assembly to Cranelift IR for dynamic recompilation.

# The Big Idea
A normal tree-walking interpreter in Rust looks like this: (pseudocode but not much)
```rust
fn eval(ast: Ast) -> usize {
    match ast {
        Literal(l) => l,
        Add(left, right) => left + right,
    }
}

let val = eval(Add(Literal(1), Literal(2)));
val // 3
```

You can instead write a *closure generator* interpreter like this, for the same language: (also pseudocode but not much)

```rust
type Environment = ();
type EvalAst = Fn(Environment) -> usize;
fn eval(ast: Ast) -> EvalAst {
    match ast {
        Literal(l) => |e: Environment| l,
        Add(_left, _right) => {
            let left = eval(_left);
            let right = eval(_right);
            |e: Environment| { left(e) + right(e) }
    }
}

let compiled_eval = eval(box Add(box Literal(1), box Literal(2)))
let env: Environment = ();
compiled_eval(env) // 3
```

`compiled_eval` look like `[ return [ return 1] + [ return 2] ]` where `[]` is its own closure.
The Add case of the closure in particular has a closed environment of `left` and `right` which are a specialized closure for the AST node that they're made of - it's just that you still need a dynamic call for evaluating them. Lineiform is a library that you'd call (probably only in a `Call` language construct, for method-level optimization) to optimize an EvalAst closure, for example inlining those `left` and `right` dynamic calls into the single function body of `compiled_eval`, since the closed environment for an EvalAst is statically known at that point.
`compiled_eval` then become `[ return 1 + 2 ]`, which you can then optimize further to just `[ return 3]` - it "unrolled" multiple interpreter loops into one function, exposing them to a recompiler for global optimization of the actual evaluation of the closure. We don't fix the `Environment` that is actually *passed* to the closure, only the closed environment.

You can think of this analogous to how a Forth compiler works: `1` is a word that pushes the value 1, `2` is a word that pushes the value 2. A dumb value of `1 2 +` then is three dynamic function calls, to function body addresses stored in its "contents" list (`1`, `2`, `+`). If you have a concretely built word at runtime, however, you can inline the calls to all the function pointers you have, and get the *actual* execution path of the function, allowing you to do global optimizations. The Rust closure `compiled_eval` looks much like this Forth word if you squint, but doesen't use a threaded interpreter execution mode, and stores the function pointers in the closure closed environment instead of a word body array.

# What Works
Currently, not much. You can create a JIT and optimize a closure, which does some janky constant propagation from the closure's environment in order to turn `jmp rax` into a statically known `jmp`, which allows us to inline. I basically only implemented as much x86 lifting as was needed for the PoC, and don't have features like "branches" or "eflags" or "calls" or "correct instruction memory widths". Don't use this yet.

# A freezing allocator
Currently we inline loads from a reference to our closed environment. This is good, but it doesn't scale: we also want to inline *functions of functions* we call, which requires us to also inline loads for closures that we are closed over. We can't just recursively inline everything from our environment, however, because our upvalues may have interior mutability that would invalidate our compiled function.
Instead, we can use a freezing allocator: all closures that are candidates for inlining you `jit.freeze(move |e: Env| { ... body ... })`, which copies it to a read-only memory region. We can then inline any loads from pointers that are inside the frozen memory region, allowing us to recursively inline environments from any closure starting point.
This has the small downside of causing segfaults if you have a `RefCell<usize>` in your environment and try to mutate it. That's a niche enough case, and easy enough to debug, that I'm just not going to worry about it: more complex interior mutable datastructures would be a pointer chase or more away, and so unfrozen and non-inlinable.

# What Needs Work
- [x] Disassembling functions
- [x] Lifting x86 to Cranelift IR
    - [ ] Enough instructions that anything non-trivial doesn't crash
- [ ] Branches
- [ ] Loops
- [ ] Calls (we need to "concretize" the SSA value map, so that an external call has the correct registers/stack, and restore them afterwards)
    - [ ] Lifting bailouts: if we hit an instruction we can't lift, we can instead bail out and emit a call to inside the original version of the function, so we can optimize only half of a complex function for example.
    - [ ] Optimistic external calls: try to use DWARF to figure out calling convention + argument count for external functions, to avoid having to spill more registers/stack than we need!
- [ ] Correct input/output function prototype detection: currently we just hardcode parameter/return value types, which is Bad.
- [ ] Freezing allocator scheme
    - [ ] *Freeing* from the frozen allocator (probably using crossbeam_epoch)
- [ ] Smarter function size fetching (currently we only search `/proc/self/exe` for them! Which doesn't work if you have any dynamic linking lol)
- [ ] Performance counters for the "optimized" Fn trait, so we only optimize over some threshold.
- [ ] A `specialize` function: we can have a variant of `optimize` that also fixes a value from the *arguments* to the closure, to for example pin the type tag of an object to erase type checks. We can compile a variant for each concrete pinned value, and emit a jump table that dispatches to either the non-compiled generic version, or the specialized variant.
