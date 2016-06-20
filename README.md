# Software Foundation Solution

Software Foundations Textbook Solution

There are some unsolved problems like 'informal proof'.

If you have any questions or find problem in solution, please tell me via [issue](https://github.com/Ailrun/software_foundations_solution/issue).

**IMPORTANT: This repository is written based on Coq8.4pl6.**  
You can download Coq8.4pl6 in [this link](https://coq.inria.fr/coq-84).

## Table Of Contents

- [Table Of Contents](#table-of-contents)
- [About Software Foundations](#about-software-foundations)
- [Table Of Solutions](#table-of-solutions)
  - [Solutions Grouped By Road Map](#solutions-grouped-by-road-map)
    - [Blue Arrow Of Road Map](#blue-arrow-of-road-map)
    - [Others Of Road Map](#others-of-road-map)
- [Whole Solutions](#whole-solutions)
- [Author Of This Solutions](#author-of-this-solutions)

## About Software Foundations

Software Foundations is the textbook for Software Foundations course in University of Pennsylvania (Pennsylvania, US) and Programming Language course in Seoul National University (Seoul, Korea) and ... (Give me additional info about).

You can download the latest version of the book in [this link](https://www.cis.upenn.edu/~bcpierce/sf/current/index.html).  
**BUT Be careful, This repository based on version 3.2, not the latest.** (*I will update in near days.*)

This book deals with not only automatic proof, but also mathematical formalization of softwares using [Coq](https://coq.inria.fr/) language. For more detail information, please check [the preface of book](https://www.cis.upenn.edu/~bcpierce/sf/current/Preface.html)

## Table Of Solutions

Status columns in next tables have one of the following values.
- Nothing : There is nothing to solve in the file.
- Solved : File is already solved. If you find any error or you have proposal, please report it using [issue](https://github.com/Ailrun/software_foundations_solution/issue)
- Unsolved : File is not solved yet.
- Unchecked : Not checked whether there is problem or not, yet.

### Solutions Grouped By Road Map

#### Blue Arrow Of Road Map

| Section Title   | Coq File                           | HTML File                                | Status    | Updated at |
|-----------------|------------------------------------|------------------------------------------|:---------:|-----------:|
| Preface         | [Preface.v](./book/Preface.v)            | [Preface.html](./book/Preface.html)           | Nothing   | 2016/06/10 |
| Basics          | [Basics.v](./book/Basics.v)             | [Basics.html](./book/Basics.html)             | Solved    | 2016/06/10 |
| Induction       | [Induction.v](./book/Induction.v)       | [Induction.html](./book/Induction.html)       | Solved    | 2016/06/10 |
| Lists           | [Lists.v](./book/Lists.v)               | [Lists.html](./book/Lists.html)               | Solved    | 2016/06/10 |
| Poly            | [Poly.v](./book/Poly.v)                 | [Poly.html](./book/Poly.html)                 | Solved    | 2016/06/11 |
| MoreCoq         | [MoreCoq.v](./book/MoreCoq.v)           | [MoreCoq.html](./book/MoreCoq.html)           | Solved    | 2016/06/11 |
| Logic           | [Logic.v](./book/Logic.v)               | [Logic.html](./book/Logic.html)               | Solved    | 2016/06/11 |
| Prop            | [Prop.v](./book/Prop.v)                 | [Prop.html](./book/Prop.html)                 | Solved    | 2016/06/12 |
| MoreLogic       | [MoreLogic.v](./book/MoreLogic.v)       | [MoreLogic.html](./book/MoreLogic.html)       | Solved    | 2016/06/13 |
| *SfLib*&#42;    | [SfLib.v](./book/SfLib.v)               | [SfLib.html](./book/SfLib.html)               | Nothing   | 2016/06/10 |
| Imp             | [Imp.v](./book/Imp.v)                   | [Imp.html](./book/Imp.html)                   | Solved    | 2016/06/13 |
| Equiv           | [Equiv.v](./book/Equiv.v)               | [Equiv.html](./book/Equiv.html)               | Solved    | 2016/06/13 |
| Hoare           | [Hoare.v](./book/Hoare.v)               | [Hoare.html](./book/Hoare.html)               | Solved    | 2016/06/14 |
| Hoare2          | [Hoare2.v](./book/Hoare2.v)             | [Hoare2.html](./book/Hoare2.html)             | Solved    | 2016/06/14 |
| Smallstep       | [Smallstep.v](./book/Smallstep.v)       | [Smallstep.html](./book/Smallstep.html)       | Solved    | 2016/06/15 |
| Auto            | [Auto.v](./book/Auto.v)                 | [Auto.html](./book/Auto.html)                 | Nothing   | 2016/06/10 |
| Types           | [Types.v](./book/Types.v)               | [Types.html](./book/Types.html)               | Solved    | 2016/06/15 |
| Stlc            | [Stlc.v](./book/Stlc.v)                 | [Stlc.html](./book/Stlc.html)                 | Solved    | 2016/06/15 |
| StlcProp        | [StlcProp.v](./book/StlcProp.v)         | [StlcProp.html](./book/StlcProp.html)         | Solved    | 2016/06/15 |
| MoreStlc        | [MoreStlc.v](./book/MoreStlc.v)         | [MoreStlc.html](./book/MoreStlc.html)         | Solved   | 2016/06/18 |
| Typechecking    | [Typechecking.v](./book/TypeChecking.v) | [Typechecking.html](./book/Typechecking.html) | Nothing | 2016/06/10 |
| References      | [References.v](./book/References.v)     | [References.html](./book/References.html)     | Solved | 2016/06/20 |
| Sub             | [Sub.v](./book/Sub.v)                   | [Sub.html](./book/Sub.html)                   | Unchecked | 2016/06/10 |
| Records         | [Records.v](./book/Records.v)           | [Records.html](./book/Records.html)           | Unchecked | 2016/06/10 |
| RecordSub       | [RecordSub.v](./book/RecordSub.v)       | [RecordSub.html](./book/RecordSub.html)       | Unchecked | 2016/06/10 |
| Postscript      | [Postscript.v](./book/Postscript.v)     | [Postscript.html](./book/Postscript.html)     | Nothing   | 2016/06/10 |

&#42; Not in blue arrow sequence, but necessary for this sequence.

#### Others Of Road Map

| Section Title   | Coq File                           | HTML File                                | Status    | Updated at |
|-----------------|------------------------------------|------------------------------------------|:---------:|-----------:|
| Rel             | [Rel.v](./book/Rel.v)                   | [Rel.html](./book/Rel.html)                   | Unchecked | 2016/06/10 |
| ProofObjects    | [ProofObjects.v](./book/ProofObjects.v) | [ProofObjects.html](./book/ProofObjects.html) | Unchecked | 2016/06/10 |
| MoreInd         | [MoreInd.v](./book/MoreInd.v)           | [MoreInd.html](./book/MoreInd.html)           | Unchecked | 2016/06/10 |
| ImpCEvalFun     | [ImpCEvalFun.v](./book/ImpCEvalFun.v)   | [ImpCEvalFun.html](./book/ImpCEvalFun.html)   | Unchecked | 2016/06/10 |
| ImpParser       | [ImpParser.v](./book/ImpParser.v)       | [ImpParser.html](./book/ImpParser.html)       | Unchecked | 2016/06/10 |
| Extraction      | [Extraction.v](./book/Extraction.v)     | [Extraction.html](./book/Extraction.html)     | Unchecked | 2016/06/10 |
| PE              | [PE.v](./book/PE.v)                     | [PE.html](./book/PE.html)                     | Unchecked | 2016/06/10 |
| HoareAsLogic    | [HoareAsLogic.v](./book/HoareAsLogic.v) | [HoareAsLogic.html](./book/HoareAsLogic.html) | Unchecked | 2016/06/10 |
| LibTactics      | [LibTactics.v](./book/LibTactics.v)     | [LibTactics.html](./book/LibTactics.html)     | Nothing   | 2016/06/10 |
| UseTactics      | [UseTactics.v](./book/UseTactics.v)     | [UseTactics.html](./book/UseTactics.html)     | Unchecked | 2016/06/10 |
| UseAuto         | [UseAuto.v](./book/UseAuto.v)           | [UseAuto.html](./book/UseAuto.html)           | Unchecked | 2016/06/10 |
| Norm            | [Norm.v](./book/Norm.v)                 | [Norm.html](./book/Norm.html)                   | Unchecked | 2016/06/10 |

## Whole Solutions

## Author Of This Solutions

Junyoung Clare Jang, Ailrun
- [Github](https://github.com/Ailrun)
- [Github Blog](https://ailrun.github.io/)
