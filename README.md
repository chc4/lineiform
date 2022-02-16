# Lineiform

Lineiform is a meta-JIT library for Rust interpreters. Given an interpreter that uses closure generation, it allows an author to add minimal annotations and calls into Lineiform in order to automagically get an optimizing method JIT, via runtime function inlining and constant propagation to resolve dynamic calls to closed environment members. Internally it does lifting of closure bodies from x86 assembly to Cranelift IR for dynamic recompilation.

# The Big Idea
(There's a [blog post](https://blog.redvice.org/2022/lineiform-rust-meta-jit/) now).

A normal tree-walking interpreter in Rust looks like this: (pseudocode but not much)
```rust
fn eval(ast: Ast) -> usize {
    match ast {
        Literal(l) => l,
        Add(left, right) => eval(left) + eval(right),
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

let compiled_eval = eval(Add(Literal(1), Literal(2)))
let env: Environment = ();
compiled_eval(env) // 3
```

`compiled_eval` look like `[ return [ return 1] + [ return 2] ]` where `[]` is its own closure.
The Add case of the closure in particular has a closed environment of `left` and `right` which are a specialized closure for the AST node that they're made of - it's just that you still need a dynamic call for evaluating them. Lineiform is a library that you'd call (probably only in a `Call` language construct, for method-level optimization) to optimize an EvalAst closure, for example inlining those `left` and `right` dynamic calls into the single function body of `compiled_eval`, since the closed environment for an EvalAst is statically known at that point.
`compiled_eval` then become `[ return 1 + 2 ]`, which you can then optimize further to just `[ return 3]` - it "unrolled" multiple interpreter loops into one function, exposing them to a recompiler for global optimization of the actual evaluation of the closure. We don't fix the `Environment` that is actually *passed* to the closure, only the closed environment.

You can think of this analogous to how a Forth compiler works: `1` is a word that pushes the value 1, `2` is a word that pushes the value 2. A dumb value of `1 2 +` then is three dynamic function calls, to function body addresses stored in its "contents" list (`1`, `2`, `+`). If you have a concretely built word at runtime, however, you can inline the calls to all the function pointers you have, and get the *actual* execution path of the function, allowing you to do global optimizations. The Rust closure `compiled_eval` looks much like this Forth word if you squint, but doesn't use a threaded interpreter execution mode, and stores the function pointers in the closure closed environment instead of a word body array.

# Lifting x86
Lineiform uses a technique called dynamic recompilation, which is used extensively in cybersecurity libraries like DynamoRIO and emulators like QEMU: by re-encoding the semantics of x86 assembly as some internal IR ("lifting"), you can treat the IR much like the IR you'd build from a normal compiler frontend. This allows you to run normal optimization passes over the IR and compile it back down to assembly again ("lowering").

Lineiform uses Cranelift's IR as its lifting target, allowing us to use its existing infrastructure to reallocate registers after our function inlining and JIT compile back to x86. This isn't really what it was built for, tbh, so it doesn't do all that great of a job currently.

## What works
You can create a JIT and feed it a closure, which does some constant propagation from the closure's environment in order to turn tailcalls and dynamic function calls into inlined basic blocks (and inline any constants that were closed over, for example) and call the resulting "optimized" closure. The x86 lifting isn't very featureful - I've implemented register aliasing, memory load/store widths, condition flags and some branching - but I haven't done any verification that any operations are correct w.r.t. actual instruction execution.

## What doesn't
The main missing lifting features are 1) it never merges divergant flow control back together 2) it doesn't handle loops at all 3) all operations are (currently) zero extended, instead of being zero or sign extended depending on the instruction. And just a whole bunch of instructions, of course, since I've mostly only been implementing exactly as much as I require to pass each test I add. C'est la vie.

# Warning
This is extremely unsafe and under construction. It will silently miscompile closures so that they return the wrong values and/or eat your socks. The entire idea of using dynamic recompilation for a JIT is ill informed and foolish; the author is the epitome of hubris. There are dragons contained within.

No license or warranty is provided. If you want to use it and care about licensing things, get in touch [on Twitter](https://twitter.com/sickeningsprawl).

# TODO list
- [x] Disassembling functions
- [x] Lifting x86 to Cranelift IR
    - [ ] Enough instructions that anything non-trivial doesn't crash
    - [ ] Tear out Cranelift and use our home-rolled Tangle IR instead
- [x] Branches
    - [ ] Merging divergant flow back together
- [ ] Loops
- [x] Calls
    - [ ] External calls (we need to "concretize" the SSA value map, so that an external call has the correct registers/stack, and restore them afterwards)
    - [ ] Lifting bailouts: if we hit an instruction we can't lift, we can instead bail out and emit a call to inside the original version of the function, so we can optimize only half of a complex function for example.
    - [ ] Optimistic external calls: try to use DWARF to figure out calling convention + argument count for external functions, to avoid having to spill more registers/stack than we need!
- [ ] Correct input/output function prototype detection: currently we just hardcode parameter/return value types, which is Bad.
- [ ] Freezing allocator scheme
    - [ ] *Freeing* from the frozen allocator (probably using crossbeam_epoch)
- [ ] Smarter function size fetching (currently we only search `/proc/self/exe` for them! Which doesn't work if you have any dynamic linking lol)
- [ ] Performance counters for the "optimized" Fn trait, so we only optimize over some threshold.
- [ ] A `specialize` function: we can have a variant of `optimize` that also fixes a value from the *arguments* to the closure, to for example pin the type tag of an object to erase type checks. We can compile a variant for each concrete pinned value, and emit a jump table that dispatches to either the non-compiled generic version, or the specialized variant.
