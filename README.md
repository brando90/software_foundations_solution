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
- [Author of this solutions](#Author of this solutions)

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
| Preface         | [Preface.v](/Preface.v)            | [Preface.html](./Preface.html)           | Nothing   | 2016/06/10 |
| Basics          | [Basics.v](./Basics.v)             | [Basics.html](./Basics.html)             | Solved    | 2016/06/10 |
| Induction       | [Induction.v](./Induction.v)       | [Induction.html](./Induction.html)       | Solved    | 2016/06/10 |
| Lists           | [Lists.v](./Lists.v)               | [Lists.html](./Lists.html)               | Solved    | 2016/06/10 |
| Poly            | [Poly.v](./Poly.v)                 | [Poly.html](./Poly.html)                 | Solved    | 2016/06/11 |
| MoreCoq         | [MoreCoq.v](./MoreCoq.v)           | [MoreCoq.html](./MoreCoq.html)           | Solved    | 2016/06/11 |
| Logic           | [Logic.v](./Logic.v)               | [Logic.html](./Logic.html)               | Solved    | 2016/06/11 |
| Prop            | [Prop.v](./Prop.v)                 | [Prop.html](./Prop.html)                 | Solved    | 2016/06/12 |
| MoreLogic       | [MoreLogic.v](./MoreLogic.v)       | [MoreLogic.html](./MoreLogic.html)       | Solved    | 2016/06/13 |
| *SfLib*&#42;    | [SfLib.v](./SfLib.v)               | [SfLib.html](./SfLib.html)               | Nothing   | 2016/06/10 |
| Imp             | [Imp.v](./Imp.v)                   | [Imp.html](./Imp.html)                   | Solved    | 2016/06/13 |
| Equiv           | [Equiv.v](./Equiv.v)               | [Equiv.html](./Equiv.html)               | Solved    | 2016/06/13 |
| Hoare           | [Hoare.v](./Hoare.v)               | [Hoare.html](./Hoare.html)               | Solved    | 2016/06/14 |
| Hoare2          | [Hoare2.v](./Hoare2.v)             | [Hoare2.html](./Hoare2.html)             | Solved    | 2016/06/14 |
| Smallstep       | [Smallstep.v](./Smallstep.v)       | [Smallstep.html](./Smallstep.html)       | Solved    | 2016/06/15 |
| Auto            | [Auto.v](./Auto.v)                 | [Auto.html](./Auto.html)                 | Nothing   | 2016/06/10 |
| Types           | [Types.v](./Types.v)               | [Types.html](./Types.html)               | Solved    | 2016/06/15 |
| Stlc            | [Stlc.v](./Stlc.v)                 | [Stlc.html](./Stlc.html)                 | Solved    | 2016/06/15 |
| StlcProp        | [StlcProp.v](./StlcProp.v)         | [StlcProp.html](./StlcProp.html)         | Solved    | 2016/06/15 |
| MoreStlc        | [MoreStlc.v](./MoreStlc.v)         | [MoreStlc.html](./MoreStlc.html)         | Nothing   | 2016/06/10 |
| Typechecking    | [Typechecking.v](./TypeChecking.v) | [Typechecking.html](./Typechecking.html) | Unchecked | 2016/06/10 |
| References      | [References.v](./References.v)     | [References.html](./References.html)     | Unchecked | 2016/06/10 |
| Sub             | [Sub.v](./Sub.v)                   | [Sub.html](./Sub.html)                   | Unchecked | 2016/06/10 |
| Records         | [Records.v](./Records.v)           | [Records.html](./Records.html)           | Unchecked | 2016/06/10 |
| RecordSub       | [RecordSub.v](./RecordSub.v)       | [RecordSub.html](./RecordSub.html)       | Unchecked | 2016/06/10 |
| Postscript      | [Postscript.v](./Postscript.v)     | [Postscript.html](./Postscript.html)     | Nothing   | 2016/06/10 |

&#42; Not in blue arrow sequence, but necessary for this sequence.

#### Others Of Road Map

| Section Title   | Coq File                           | HTML File                                | Status    | Updated at |
|-----------------|------------------------------------|------------------------------------------|:---------:|-----------:|
| Rel             | [Rel.v](./Rel.v)                   | [Rel.html](./Rel.html)                   | Unchecked | 2016/06/10 |
| ProofObjects    | [ProofObjects.v](./ProofObjects.v) | [ProofObjects.html](./ProofObjects.html) | Unchecked | 2016/06/10 |
| MoreInd         | [MoreInd.v](./MoreInd.v)           | [MoreInd.html](./MoreInd.html)           | Unchecked | 2016/06/10 |
| ImpCEvalFun     | [ImpCEvalFun.v](./ImpCEvalFun.v)   | [ImpCEvalFun.html](./ImpCEvalFun.html)   | Unchecked | 2016/06/10 |
| ImpParser       | [ImpParser.v](./ImpParser.v)       | [ImpParser.html](./ImpParser.html)       | Unchecked | 2016/06/10 |
| Extraction      | [Extraction.v](./Extraction.v)     | [Extraction.html](./Extraction.html)     | Unchecked | 2016/06/10 |
| PE              | [PE.v](./PE.v)                     | [PE.html](./PE.html)                     | Unchecked | 2016/06/10 |
| HoareAsLogic    | [HoareAsLogic.v](./HoareAsLogic.v) | [HoareAsLogic.html](./HoareAsLogic.html) | Unchecked | 2016/06/10 |
| LibTactics      | [LibTactics.v](./LibTactics.v)     | [LibTactics.html](./LibTactics.html)     | Nothing   | 2016/06/10 |
| UseTactics      | [UseTactics.v](./UseTactics.v)     | [UseTactics.html](./UseTactics.html)     | Unchecked | 2016/06/10 |
| UseAuto         | [UseAuto.v](./UseAuto.v)           | [UseAuto.html](./UseAuto.html)           | Unchecked | 2016/06/10 |
| Norm            | [Norm.v](./Norm.v)                 | [Norm.html](Norm.html)                   | Unchecked | 2016/06/10 |

## Whole Solutions

## Author of this solutions

Junyoung Clare Jang, Ailrun
- [Github](https://github.com/Ailrun)
- [Github Blog](https://ailrun.github.io/)
