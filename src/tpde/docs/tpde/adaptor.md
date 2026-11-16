\page tpde-adaptor IRAdaptor Reference

The IRAdaptor is a class that you as a user will need to implement such that the framework can access
information about the structure of your IR. The compiler implementation will be templated on the class type
and you will need to pass in a pointer to an instance of that class to the CompilerBase.

The main requirements posed on the IR by the framework are:
- SSA form w.r.t. instructions, e.g. memory does not need to be in SSA form
- a control flow graph of basic blocks with control flow operations (not calls) only at the end
- a list of instructions in each basic block
- instructions can have multiple input and output values
- functions and basic blocks have a single entry point
- values are unified at edges using PHI nodes (direct support for block arguments is planned)

The class you provide will be typechecked against a concept which is described in [IRAdaptor.hpp](@ref tpde/include/tpde/IRAdaptor.hpp).
Please see it for descriptions of functions and types required along with their required
functionality.

<div class="section_buttons">
 
| Previous          |                              Next |
|:------------------|----------------------------------:|
| [Overview](@ref tpde-overview) | [Compiler Reference](@ref tpde-compiler-ref) |
 
</div>

