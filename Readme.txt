Release notes

List of changes

==============================================
21aug02  Version 2.00 - first released version
==============================================

06oct02  SuperLieSing`: control the order of terms (sgLess)

10nov02  Revised package SuperLie`Cohom`. Added functions chNext and chBook

10nov02  Package SuperLie`Domain`: Enhanced format properties.

         Added function ClearFormat

17nov02  HWModule: added PDim property

24nov02  Added standard grading Homogen and Parity

         New property Mapping

         VectorLieAlgebra: new regradings (denoted by negative numbers)

08dec02  CartanMatrixAlgebra: The basis and the relations are now assigned at
         every step, so they are available if the calculation was aborted.

15dec02  EnvelopingSymbol: fixed a bug.

         DiffAlgebra: set the parity of the bracket to 0.

22dec02  Fixed operations on functions such as (f1+f2)[x,y]

         Functions P, Parity, Deg, Grade, Weight, PolyGrade: declared arguments

==============================================
24dec02  Version 2.01 released
         Added reference guide and examples
==============================================

05jan03  Fixed TCollect

         RestrictModule: added debug printing

19jan03  Fixed a bug in SubSpace: if the parity was not defined in the space,
         the subspace was assumed even. 

19jan03  Fixed bug in chNext: chNext[deg] did not work with explicit degree.

20jan03  Created home page www.equaonline.com/math/SuperLie

26jan03  Fixed diagnostic messages for PoissonAlgebra and related functions.

05apr03  Fixed "Loaded" message in Vecfield.m anf Subalg.m

18may03  Function chInSol now accepts list of vectors in second argument.

         Fixed bug in DefSubAlgebra. Better diagnostic about generated elements.


==============================================
21may03  Version 2.02 released
         The documentation is revised
==============================================

01jun03  New constructor HamiltonAlgebra.

         Regradings of Poisson algebra with integer parameter
         (as for VectorLieAlgebra).

14sep03  CartanMatrixAlgebra: The function PolyGrade was not defined on
         diagonal elements. Fixed. More debug messages added.

         Fixed VSolve to work with single (non-list) unknown and with
         extra (more than 2) arguments.

         Added VerifySolutions->False to Solve[..., InverseFunctions->True]
         (because otherwise it does not work in Mathematica 5.0)

         Fixed "Loaded" messages at the end of  *.m files

30sep03  Changed wrong symbol names
         FactorModule -> QuotientModule (function)
         Factor -> Quotient (option)
         EnveloppingSymbol -> EnvelopingSymbol (function)
         EnveloppingOperation -> EnvelopingOperation (function)

         The functions RDer and ZRDer removed.

12oct03  The default of $SNormal changed from Expand to Together

18oct03  Fixed order of evaluation of relations in case of generators with 
         different or negative gradings.

19oct03  Package Cohom`: new argument of chSetAlg - the module of coefficients
         Added defaults for ch$raise, ch$lower, chSplit.
         chBasis[d] used only if no coef. module defined in chSetAlg
         Function chPos[] returns the current position in the process of calculation.

         Changed InfixFormat (the precedence did not work).
         Group option removed.
         Subscripted output in Standard form made readable.
         Fixed removing format

31oct03  Fixed property Jacobi->{op1,...} so that it is applied to every element of
         the list (that allows using special rules for operations)

07dec03  Changed order of generation of Z-graded algebras, now the graded components
         are calculated consecutively (the old order was by the degree in terms of
         generators). This allow having zero-graded generators.

14dec03  Enhancements in output format

20jan04  Enhanced svSolve

18apr04  New functions for CartanMatrixAlgebra: CartanMatrix, RootReflection,
         WeightToPolyGrade, PolyGradeToWeight (not yet documented)

25apr04  HWModule[m,g,lambda] builds module with highest weight (lambda[1],...,lambda[n]).

         HWModule and CommutativeLieAlgebra enumerate the basis of the module.


==============================================
27apr04  Version 2.03 released
==============================================

13jun04  Fixed small bugs in generation of mudules-relatives

13jun04  Fixed bug in VectorLieAlgebra

30jun04  Package Cohom`: new function chCalcMore calculates next cohomology

18sep04  Fixed action of algebra built from Cartam matrix on sub- and quotientmodules

18sep04  QuotientModule now support Mapping option and MappingRule

02jan05  Defined P[LDer[...]]

         Function SameElement is now exported. LDer may differentiate over elements of
         basis of monomials

         Fixed output format for CircleTimes with single argument.

         Fixed Domain of arguments. The form with 3 arguments has now default definition
         via 2-argument form (with second argument First, Last, All). The existing definitions
         op/: Domain[op,All]:=... changed to op/: Domain[op,_]:=... .

28mar05  Option WList to space constructor gives the weigths of generators.

         Fixed LinearCollectRule to work with non-sorted sums.

         Option Clear->True keeps now the list of defined spaces-relatives.

02apr05  Fixed the action of algebras defined from Cartan matrices on any modules (was defined
         only for modules built from highest or lowest vectors)

17apr05  New method for function GradeBasis, with a symbol as the first argument.
         GradeBasis[fn, vars, op] defines function fn[deg] => basis of degree deg. This function
         stores intermediary results and therefore is faster if called repeatedly.

19apr05  Fixed regrading of Poisson algebra

24apr05  Fixed operation in enveloping algebra

06may05  Fixed action of vector fields on tensors

28may05  Fixed bug i GradedSubAlgebra (failed ir some cases)

==============================================
08jul05  Version 2.04 released
==============================================

04sep05 Fixed property Wedge in VectorLieAlgebra

13nov05 Fixed problems in properties

13nov05 New version of functions that generate polynomial basis:
  DegreeBasis, UpToDegreeBasis, GradeBasis, FilterBasis
  The new version is faster and accept more options.

24mar06 Added functions for working with fields of characteristic p>0:
  FieldChar, DivPowers, DivPowersQ, UnDivPowers

24mar06 Added function for solving equations with non-linear parameters:
  ParamSolve

26mar06 Fixed Mapping option in QuotientModule

==============================================
26mar06  Version 2.05 released
==============================================

09sep06 Function HWModule: support for characteristic >=3. Mode debug printing.

        In ScalarEquations the the result is normalized (to exclude trivial
        equations in case of fields of positive characteristic)

12nov06 The last argument of CartanMatrixAlgebra changed to option GRange->rn

        The argument "whole" of QuotientModule changed to option Module->...
        Fixed the description in the documentation.

        Fixed some formatting problems in About and Information (do not evaluate
        when printing hold forms)

        Added new functions for working with general sums:
        GeneralImage, GeneralKernel, GeneralInverseImage, GeneralPlus,
        GeneralDim, GeneralAct, GeneralIntersection

        New function QuotientAlgebra

19nov06 Added support for fields of characteristic 2 (operation and option Squaring)
        Modified: SubAlgebra, FreeLieAlgebra, CartanMatrixAlgebra,
        glAlgebra, slAlgebra, pslAlgebra, qAlgebra, sqAlgebra, q2Algebra(?), 

10dec06 ActTable and SqrTable made public
        HWModule with option Grade->Auto (later replaced with ToGrade)
        Fixed bug in LinearCollectRule

12dec06 Revised SuperLie`Sing`.
        New function: svUnSub.
        New data objects: sv$Print, sv$hi; sv$eqHi; sv$eqZ; sv$e;
        Subscripted format for scalar coefficients
        svVerma does not reqiure 3-rd argument (the depth of calculations)
        svSolve returns "True", "No solutions" "Cannot solve" or a non-empty
        list of sloutions

13dec06 Options ToDegree and ToGrade limits the calculations (instead of GRange
        and Grade what was not always used consistently). The degree parameter
        in CartanMatrix algebra and FreeLieAlgebra also replaced (but still work
        for backward compatibility)


25dec06 Fixed bug in LinearCollectRule
        Fixed PiOrder
        Fixed PiLeft (was Times instead of SVTimes)
        SubModule: use VNormal before LinearChange; do not pass some options to SubSpace
        QuotientModule: fixed Ideal option; do not pass some options to VectorSpace

26dec06 Added SuperLie`ShapDet` and SuperLie`Det`

27dec06 Wedge may be symmetric or skew-symmetric (by default symmetric)
        Different types of symmetry cancel each other.
        
18feb07 Fixed option ToGrade in HWModule
        Partial support of singular vectors in char>0
        
25mar07 Fixed bug in Ideal for char=2
        
08apr07 Use chCalc[deg,-r] instead of chCalc[deg,r] to save memory (not
        possible to continue the calculation of cohomology using chCalcMore)
        
        Added debug output to ApplySplit and MapSplit
        
22apr07 Fixed ActTable for Ideal and QuotientAlgebra 

        Fixed BracketMode for Ideal, QuotientAlgebra, DefSubAlgebra

06jun07 ParamAssume[code] executes the code and collects all assumption
        made by ParamSolve while solving equations.

19aug07 CartanMatrixAlgebra: add extra rows to the matrix to extend the algebra
        with exterior derivatives

28oct07 wPower[x,n] = x /\ x /\ ... x (n times). Supports divided powers
        (execute DivPowers[x->wPower] to use divided powers)
        
25nov07 Set wedge[x] = x (to avoid ambiguily).

        DateString defined now for Mathematica <6.0 only. Mathematica 6.0 has it.
        
        Removed redundant definitions of SameElement.

27nov07 chSetAlg supports options. The options are passed to DLeft.
        
02dec07 Fixed output format and other compatibility issues for Mathematica 6.0        

        wPower by default is not divided even for characteristic 2.

16dec07 Added initial version or package for calculations with sparse arrays

17feb08 Fixed bugs in sparce calculations

06jul08 Fixed messages in Sing.m

18feb09 Fixed HWModule in case of weight with parameter (using special
        rating function for selecting variables in ParamSolve)

17aug09 Fixed divided powers of non-monomials

06sep09 Fixed Contact algebra k(1+2m|2n) for char=2 

==============================================
08sep09  Version 2.06 released (as Preview 7)
==============================================

31aug11 Fixed compatibility of ModSolve with Mathematica 8

02oct11 Fixed bug in CartanMatrixAlgebra

08jul13 $ParamAssume collects assumptions made by ParamSolve.
        Trying to minimize the number of assumptions in case FielsChar > 0

10jul13 Using LinearChange instead of ReplaceAll in SubModule

14jul13 "General" functions works now with splitted sums

14jul13 Fixed bug in SubModule that made it very slow.

14jul13 ApplySplit supports extra arguments

18jul13 Added palette with Help button (because F1 does not work with add-ons
        in Mathematica 8.0)

==============================================
21jul13  Version 2.07 released 
==============================================

24oct14 Fixed compatibility with Mathematica 9. In case of conflicting symbols
        the SuperLie symbols will shadow the Mathematica symbols.

19jul15 Fixed redefinition of symmetry of Wedge
        Added version of HamiltonAlgebra with explicit struclure constants

25oct15 Fixed action of algeras with Cartan matrix on CoLeft[module]

01dec15 Fixed HWModule for characteristic 2

10jan16 SubAlgebra: Checking if the generators are graded
        (unless a new grading is defined in subalgebra).

==============================================
21jul16  Version 2.08 Beta 01
==============================================

04dec16 glAlgebra, slAlgebra:
          Fixed list or relatives
        TensorSpace:
          Defined properiies Dim, P, Grade, TheAlgebra;
          For tensor spaces of a module, defined the action the module's algebra.

12dec16 HWModule:
          Fixed case when y_i was expressed via y_j with j>i
          Added properties TheAlgebra and Relatives

14may17 NewRelative: Added property Basis
        (?) Der, Der0: fixed case when Wedge is skew-symmetric

04mar18 Fixed bugs in change 25oct15

03may18 SubAlgebra: fixed case when all generators have garde > 1.

==============================================
06may18  Version 2.08 Beta 02
==============================================