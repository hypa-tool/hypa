# HyPA: Hyperproperty Verification with Predicate Abstraction Beyond k-safety 

This repository contains HyPA (short for **Hy**perproperties **P**redicate **A**bstraction), a tool that can verify `\forall^*\exists^*` hyperproperties on infinite-state systems within a given (predicate) abstraction.
It builds on the theory presented in 
> Raven Beutner and Bernd Finkbeiner. Software Verification of Hyperproperties beyond k-safety. CAV 2022 [1]


## HyPA Overview

HyPA is a tool that can verify hyperproperties on infinite-state systems.
It specializes on `\forall^k\exists^l` safety hyperproperties (for some `k`, `l`) which state that for all `k` traces there exist `l` traces such that the resulting `k+l` traces do not interact badly. 
k-safety properties are the *special case* where `l = 0`. 

HyPA reads a symbolic transition system, the hyperproperty to be checked, and a set of predicates and determines if the property can be verified within the given abstraction.
To this end, HyPA uses the provided predicates to construct an abstraction of the system (parametrized by the scheduling in each step)and turns the abstraction into a game which is subsequently solved.
As shown in [1], if the safety player wins the constructed game, the system satisfies the property. 

## Structure 

- `src/` contains the source code of HyPA written in F#.
- `benchmarks/` contains the benchmarks used in [1] to evaluate HyPA.
- `app/` is the target folder for the build. It contains a `config.conf` file that should point to a local Z3 installation (see Section [Build and Connect Z3](#build-and-connect-z3s)).

## Build And Run HyPA

To build and run HyPA you need the following

- [.NET 6 SDK](https://dotnet.microsoft.com/en-us/download) (tested with version 6.0.202)
- [Z3](https://github.com/Z3Prover/z3) (tested with version 4.8.17)


### Build HyPA
To build HyPA run the following (when in the main directory of this repository).

```shell
cd src
dotnet build -c "release" -o ../app
cd ..
```

Afterwards, the HyPA executable is located in the `app/` folder.
Note that the HyPA executable is not standalone and requires the other files located in the `app/` folder.
In particular, to copy the executable, you need to copy the entire contents of the `app/` folder (we recommend to just leave it where it is).


### Build and Connect Z3 

HyPA requires the [Z3](https://github.com/Z3Prover/z3) SMT solver. 
HyPA is designed such that it only needs to the *path* to the Z3 executable, so everyone can install Z3 whereever it fits them best.
Either build Z3 yourself or download a prebuilt binary for your architecture (see [here](https://github.com/Z3Prover/z3/releases)).

The absolute path to Z3 is specified in the `config.conf` configuration file.
This file **must** be located in the same directors as the HyPA executable (this convention makes it easy to find the config file, independent of the relative path HyPA is called from).
We already provide a config file `app/config.conf`.
After having built (or downloaded) Z3, paste the **absolute** path to the Z3 solver into the `config.conf` file.
For example, if the Z3 binary is `/usr/bin/z3`, change the content of `app/config.conf` to 

```
[z3Path]
/usr/bin/z3
```


### Run HyPA

After having built HyPA and set the path to the Z3 solver, invoke HyPA by running
 
```shell
./app/HyPA -i inputfile.hypa
```

where `inputfile.hypa` is the (path to the) input problem that should be verified.

### A First Example 

As a first example consider the program in Figure 2 of [1] which is located in `benchmarks/ksafety/paper_example_fig2`.
Run

```shell
./app/HyPA -i benchmarks/ksafety/paper_example_fig2/paper_example_fig2.hypa
```
which should successfully verify the property.

We give more details on the input of HyPA in the section [Input to HyPA](#input-of-hypa) below.
Further examples are located in the `benchmarks/` folder.


## Input of HyPA

HyPA supports several command line options.

- `-i` sets the path to the verification instance (usually this is a `.hypa` file). The `.hypa` file then points to the system, property and predicates that should be used for this instance. This option is mandatory. See Section [Hypa File](#hypa-file) below, for details on the structure of the `.hypa` file.
- `-v` determines the verbosity level of HyPA. The available options are 0 (only output the result), 1 (output the data used for evaluation in [1]), 2 (output the result as well as intermediate steps), and 3 (debug output). The `-v` option is optional. If not used, the verbosity level is set to 2 by default. 
- `-s` sets the solver used by HyPA to solve games for `\forall^*\exists^*` instances (i.e., instances beyond k-safety). Available options are `naive` (to use the naive solver) and `lazy` (to use the more efficient lazy solver, presented in [1]). The `-s` option is optional. If not used, the `lazy` solver is used by default. The solver option is only relevant for properties that use existential quantification, i.e., properties of the form `\forall^k\exists^l` with `l >= 1`. The (default) `lazy` solver is always superior to the `naive` solver, so there is seldom a reason to make use of the `-s` option. 


### Hypa File 

A verification instance for HyPA consists of a list of symbolic transition systems, a hyperproperty and a set of predicates.
To maintain everything in a modular way, they are split across multiple files. 
A `.hypa` file contains a single verification instance and points to external files that contain the symbolic transition systems (STS), the automaton and the predicates that should be used.
A `.hypa` file must contain the following categories (in this order):

- `[systems]`: a list of files for the systems
- `[automaton]`: a file that contains the safety automaton
- `[qs]`: the quantifier structure of the hyperproperty given as a pair (k, l), representing a `\forall^k\exists^l` property.
- `[preds]`: a file that contains the predicates that should be used
- `[comment]`: additional comments for this verification problem, ignored by HyPA

As an example, we consider the example in Figure 2 from [2] which is located in `benchmarks/ksafety/paper_example_fig2`.
The content of `paper_example_fig2.hypa` is the following:

```
[systems]
[ts1, ts2]

[automaton]
aut

[qs]
(2, 0)

[preds]
preds

[comment]
...
```

In this case, the files `ts1`, `ts2` `aut` and `preds` should be located in the *same* directory as the `paper_example_fig2.hypa` file. 
The above specifies a `\forall^2` property (since the quantifier structure is `(2, 0)`), where the body of the property is given as the safety automaton in `aut`.
The property is checked against the STSs in `ts1` and `ts2` (where the first trace is resolved on `ts1` and the second on `ts2`). In general, the same transition system can appear multiple times.
The number of STS appearing under `[systems]` must be equal to `k+l`, where `(k, l)` is the quantifier structure. 
`preds` contains the predicates that should be used for verification.

Next, we describe how to specify STSs, automata and predicates, again on the example from Figure 2 in [1].
Formulas (used, e.g., in guards and updates) follow the [SMTLIB](https://smtlib.cs.uiowa.edu/) standard in which formulas are written in prefix notation.
For example, `(> (+ 1 x) y)` represents the formula `1 + x > y`.


#### Specification of STSs

Consider the following program from Figure 2a in [1]:

```
x = 1
repeat 
    y = 2 * x
    while y > 0 do
        y = y - 1; 
        x = 2 * x
```

We represent this program as the following STS (the content of `ts1`)

```
[vars]
{x, y}

[locations]
{0, 1, 2}

[init]
(0: true)

[step]
0:
    {
        (true, [x := 1], [|], 1)
    }

1:
    {
        (true, [y := (* 2 x)], [|], 2)
    }

2:
    {
        ((> y 0), [y := (- y 1), x := (* 2 x)], [|], 2)
        ((<= y 0), [], [|], 1)
    }

[obs]
(1: true)
```

The `[vars]` category defines all variables used in the program (all variables have type `int`). 
`[locations]` defines all control locations of the system.
`[init]` is a partial mapping from locations to formulas that define conditions on the initial state.
In this case, we start at location 0, with any assignment to the variables (as the formula is `true`). If we would, for example, set `(0: (> x y))` the program can start at location 0 with any variable assignment where `x > y`.
`[step]` defines the transitions of the program. Each location is associated with a set of outgoing edges.
Each edge has the form `(g, [A_1, A_2, ...], [x1 x2 ... | F], t)` where `g` is a guard (an SMT formula over the variables), `A_1, A_2, ...` are assignments to variables (for example `y := (- y 1)` decrements `y` by 1).
`x1 x2 ...` are program variables that are choose non-deterministically, i.e., they can take on any value (they may therefore *not* appear in the left hand side of any assignment).
`F` is a general formula that specifies further restrictions on the post state (by ranging over primed and unprimed variables).
For most cases, the additional condition `F` and the non-deterministic variables `x1 x2 ...` are not needed. 
A typical transition thus has the form  `(g, [A_1, A_2, ...], [|], t)`.
If a variable does not appear on the left-hand-side of any assignment (and not in the list of non-deterministically chosen variables), its value remains unchanged. 
Lastly `t` is the target location of that transition.

It should be straightforward to map the above STS to the pseudo program.

Lastly, `[obs]` defines the points at which the program execution is observed in our logic (see the definition of OHyperLTL in [1]). Using `[obs]` is analogous to the use of `[init]`. In our example, we observe the program whenever in location 1 (as the formula is set to `true`). 

#### Specification of Safety Automata

We consider the LTL specification `(x_0 = x_1) => G (x_0 = x_1)`, where `x_0` refers to the value of `x` in the program bound to the first trace (resolved on `ts1`) and `x_1` to the value of `x` in the second trace.
See the example in [1].
We represent this formula as a safety automaton. 
The content of `aut` is the following:

```
[states]
{0, 1, 2}

[initial]
{0}

[bad]
{2}

[vars]
{x_0, x_1}


[edges]
0: 
    {
        ((= x_0 x_1), 1)
    }

1: 
    {
        (true, 1)
        ((not(= x_0 x_1)), 2)
    }

```

We specify a set of states (`[states]`) a set of initial states (`[initial]`) and a set of bad states (`[bad]`).
We also include the set of variables used (`[vars]`).
Similar to the definition of a STS, the edges of an automaton are given per state.
An edges has the form `(g, t)` where `g` is a guard ranging over those variables appearing in `[vars]` and `t` is the target state of that transition.
Note that in an STS all formulas range over variables in that system, whereas the variables in the automaton are annotated by a number that indicates to which copy it refers (i.e, variables have the form `x_i`).
An automaton accepts a word (a sequence of assignments to the variables), if there exists *no* run that visits a bad state (see [1]).

#### Specification of Predicates

Lastly, we specify the predicates per location in the product program. 
Tracking predicates locally allows to reduce the size of the abstract system.
In our example, `preds` contains the following: 

```
[1 1]:
{
    (= x_0 x_1)
}

[2 2]:
{
    (= x_0 x_1),
    (= y_0 (* 2 y_1)),
    (= x_1 (* 2 x_0)),
    (= y_0 (+ (* 2 y_1) 1)),
    (and (>= y_0 0) (>= y_1 0))
}
```

For a location in the product (e.g., the location `[1 1]` is the state where both instances are in location 1), we assign a set of predicates (separated by a comma).
For states not appearing, the set of predicates is empty.
It is possible to group multiple product locations together and thus specify predicates for multiple locations at once.
For example

```
[0 0] [1 1]:
{
    (= x_0 x_1)
}
```

sets the predicates for locations `[0 0]` and `[1 1]` at the same time. 

We require that the predicates are precise enough to describes the initial conditions (the formulas used in the `[init]` block of the transition system), the observation formulas (the formulas used in the `[obs]` block of the transition system), and the formulas used in the automaton edges (see [1]).
If the predicates are not precise enough at some location, HyPA will raise an error during evaluation. 


## References

[1] Raven Beutner and Bernd Finkbeiner. Software Verification of Hyperproperties beyond k-safety. CAV 2022