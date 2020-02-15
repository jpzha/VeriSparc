# A Framework for Modular Verification of SPARCv8 Code 

All the Coq implememtations are in the direction /coqimp 

### File Structure
**/coqimp/framework:** 
- /auxiliary : some auxiliary definitions like integer
- /models : the program model including the registers, memory, operational semantics and so on
- /logic : assertion definitions and logic rules
- /soundness : soundness prove

**/coqimp/ext**
- lowlang.v : the definitions about low-level language
- highlang.v : the definitions about high-level language
- rellogic.v : the extended program logic supporting refinement verification
- refinement.v : define the event trace refinement, state relation between low- and high-level program, and the primitive correctness
- lemmas_comp.v lemmas_comp2.v : lemmas for compositionality
- compositionality.v : logic soundness ensures contextual refinement 
- rellogic_soundness.v : logic soundness proof
- finaltheorem.v : logic ensures contextual refinement

**/coqimp/example:** 
- /code : the codes need to be proved
- /lib : some tactics and derived rules
- /spec : code specifications
- /proof : the proofscripts

### Compilation Coq files
Require Coq.8.9.1 and use "make all" command under folder /coqimp to compile all the coq files

### Coq Installation 
[Install Coq with opam](https://coq.inria.fr/opam-using.html)
