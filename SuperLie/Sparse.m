BeginPackage["SuperLie`Sparse`", {"SuperLie`", "SuperLie`Domain`",
    "SuperLie`Enum`", "SuperLie`Space`", "SuperLie`Submod`", 
    "SuperLie`Envsort`", "SuperLie`Genvect`", "SuperLie`Generate`", 
    "SuperLie`Vsplit`", "SuperLie`Subalg`", "SuperLie`Symalg`", 
    "SuperLie`Irrmod`"}]
(*
This package works with sparse array representation of algebras
*)

SuperLie`Sparse`ActToSparse::usage = "ActToSparse[g] returns the structural constants \!\({\(C\^k\)\_\(i\[InvisibleComma]j\)}\) of the bracket on the algebra g as a sparce array."

SuperLie`Sparse`SquaringToSparse::usage = "SquaringToSparse[g] returns the structural constants \!\({\(S\^k\)\_i}\) of the squaring operation on the algebra g as sparce array."

SuperLie`Sparse`FormToSparse::usage = "FormToSparse[\[Omega]] returns the sparce-array representation of the form \!\(\[Omega]\[Element]\[GothicM]\[CircleTimes]\(\[CapitalLambda]\^k\)\[GothicN]\) where \!\(\[GothicM]=\[LeftAngleBracket]m\_i, i\[Element][1,dim(\[GothicM])]\[RightAngleBracket]\) and \!\(\[GothicN]=\[LeftAngleBracket]n\_i, i\[Element][1,dim(\[GothicN])]\[RightAngleBracket]\) a finite-dimensional modules over a Lie (super)algebra."

SuperLie`Sparse`PowerToSparse::usage = "PowerToSparse[\[Omega]] returns the sparce-array representation of coefficients \!\(c\_\(i\[InvisibleComma]j\)\) of the form \!\(\[Omega]=c\_\(i\[InvisibleComma]j\) m\_i\[CircleTimes]\(n\_j\)\^\(\[Wedge]k\) + ...\[Element]\[GothicM]\[CircleTimes]\(\[CapitalLambda]\^p\)\[GothicN]\) where \!\(\[GothicM]=\[LeftAngleBracket]m\_i, i\[Element][1,dim(\[GothicM])]\[RightAngleBracket]\) and \!\(\[GothicN]=\[LeftAngleBracket]n\_i, i\[Element][1,dim(\[GothicN])]\[RightAngleBracket]\) a finite-dimensional modules over a Lie (super)algebra. The members of form \[Omega] that are not powers (e.g., \!\(m\_k\[CircleTimes]n\_i\[Wedge]n\_j\) for i!=j) are ignored."

SuperLie`Sparse`TestSparseBracket::usage = "TestSparseBracket[g,c] tests that \!\(c={\(C\^k\)\_\(i\[InvisibleComma]j\)}\) are structure constant of a valid superalgebra bracket on g. TestSparseBracket[g,c,s] tests also the structure constants \!\(s={\(S\^k\)\_i}\) of squaring operation on g"

Begin["$`"]

(*Convert Act and Squaring to sparse arrays C^k_ij and S^k_j *)

ActToSparse[g_, opts___] :=
 Module[{ar, brk, gdim, i, j, b, setSpAct},
  setSpAct[SVTimes[cf_, g[k_]]] := (ar[[k, i, j]] = cf);
  setSpAct[g[k_]] := (ar[[k, i, j]] = 1);
  gdim = Dim[g];
  ar = SparseArray[{}, {gdim, gdim, gdim}];
  brk = Bracket[g];
  For[i = 1, i <= gdim, i++,
    For[j = 1, j <= gdim, j++,
     b = VNormal[brk[g[i], g[j]]];
     If[b =!= 0,
      setSpAct /@ VPlusTerms[b]]]];
   Clear[setSpAct];
  ar]

SquaringToSparse[g_, opts___] :=
 Module[{ar, brk, gdim, i, j, b, setSpAct},
  setSpAct[SVTimes[cf_, g[k_]]] := (ar[[k, i]] = cf);
  setSpAct[g[k_]] := (ar[[k, i]] = 1);
  gdim = Dim[g];
  ar = SparseArray[{}, {gdim, gdim}];
  brk = Bracket[g];
  For[i = 1, i <= gdim, i++,
   If[P[g[i]] == 1,
    b = VNormal[Squaring[g[i], brk]];
    If[b =!= 0,
     setSpAct /@ VPlusTerms[b]]]];
  Clear[setSpAct];
  ar]


(*Convert cocycle to sparse array *)

FormToSparse[expr_, opts___] :=
 Block[{$fsAr = SparseArray[{}, modDim[expr]],
        $fsDiv = DivPowers/.{opts}/.DivPowers->False},
  setSC[VNormal[expr]];
  $fsAr]


PowerToSparse[expr_] :=
 Block[{$fsAr = SparseArray[{}, sqrDim[expr]]},
  setSqr[VNormal[expr]];
  $fsAr]

(*Auxiliary functions*)

(* Calculate components of C^k_{ij} *)

setSC[expr_VPlus] := Scan[setSC, expr]
setSC[SVTimes[c_:1, expr_]] := setSCf1[ck2list[expr], c]

setSCf1[{_[i_], x_[j_]}, c_] :=
  $fsAr[[i, j]] = c;

setSCf1[{_[i_], x_[j_], y_[k_]}, c_] :=
 If[j == k, 
  $fsAr[[i, j, k]] = If[$fsDiv, c, 2*c],
 (*else*)
  $fsAr[[i, j, k]] = c;
  $fsAr[[i, k, j]] = -(-1)^((P[x[j]]+1) (P[y[k]]+1)) c]


ck2list[x_ ** y_] := Join[ck2list[x], ck2list[y]]
ck2list[x_wedge] := Flatten[ck2list /@ List @@ x]
ck2list[wPower[x_, k_]] := Flatten[Table[ck2list[x], {k}]]
ck2list[x_[i_]] := {x[i]}

(* dimensions of modeles used in the form *)

modDim[VPlus[x_, __]] := modDim[x]
modDim[SVTimes[_, x_]] := modDim[x]
modDim[x_ ** y_] := Join[modDim[x], modDim[y]]
modDim[x_wedge] := Flatten[modDim /@ List @@ x]
modDim[wPower[x_, k_]] := Flatten[Table[modDim[x], {k}]]
modDim[x_] := {Dim[TheModule[x]]}

(* Calculate components of S^k_i *)

setSqr[expr_VPlus] := Scan[setSqr, expr]
setSqr[SVTimes[c_: 1, x_ ** wPower[y_, _]]] := setSqrCf[x, y, c]

setSqrCf[_[i_], _[j_], c_] := ($fsAr[[i, j]] = c)

(* dimensions of modeles used in the form *)

sqrDim[VPlus[x_, __]] := sqrDim[x]
sqrDim[SVTimes[_, x_]] := sqrDim[x]
sqrDim[x_ ** y_] := Join[modDim[x], sqrDim[y]]
sqrDim[wedge[x_,___]] := sqrDim[x]
sqrDim[wPower[x_, k_]] := sqrDim[x]
sqrDim[x_] := {Dim[TheModule[x]]}


(*Testing Jacobi identity*)

TestSparseBracket::sym = "The bracket is not (super)antisymmetric"
TestSparseBracket::jac = "The Jacobi identity for bracket is not valid"
TestSparseBracket::sqr = "The Jacobi identity for squaring is not valid"

SparseNonZero[s_] := s!=SparseArray[{},Dimensions[s]];

TestSparseBracket[g_,c_] :=
  Which[
    SparseNonZero[SymTst[g,c]], Message[TestSparseBracket::sym]; False,
    SparseNonZero[JacTst[g,c]], Message[TestSparseBracket::jac]; False,
    True, True];

TestSparseBracket[g_,c_, s_] :=
  And[ TestSparseBracket[g,c],
       If[SparseNonZero[SqrTst[g,c,s]],
           Message[TestSparseBracket::sqr]; False,
           True]]
  

(* Apply the sign rule *)

JacSgn[alg_,cc_]:=SparseArray[JacSgnIJ[alg,#]&/@ArrayRules[cc],Dimensions[cc]]
JacSgnIJ[alg_,i_->v_]:=i->(-1)^(P[alg[i[[2]]]]P[alg[i[[3]]]]) v


(* Jacobi identity test. Calculates [f,[g,h]]-[[f,g],h]-(-1)^(P(f)P(g))[g,[f,h]] as a sparse array.
 If the Jacobi identity is correct, the result should be SparseArray[<0>,{n,n,n,n}] where
 n = Dim (\[GothicG]).*)

JacTst[alg_,c_] := 
   SparseArray[Map[$SNormal,c.c-Transpose[Transpose[c,{3,2,1}].Transpose[c,{2,1,3}],{3,2,1,4}]-JacSgn[alg,Transpose[c.c,{1,3,2,4}]],{4}]]


(*Symmetry test. Calculates [f,g]+(-1)^(P(f)P(g))[g,f] as a sparse array. If C^k_{ij} is antisymmetric,
 the result should be SparseArray[<0>,{n,n,n}] where n = Dim(g).*)


SymTst[alg_,c_]:=SparseArray[Map[$SNormal,c+JacSgn[alg,Transpose[c,{1,3,2}]],{3}]]


(*Jacobi identity test for squaring. Calculates [[f,g],g]-[f,g^{[2]}] as a sparse array.
 If the Jacobi identity is correct, the result should be SparseArray[<0>,{n,n,n}] where n=Dim(g)*)


SqrTst[alg_,c_,s_]:=SparseArray[Map[$SNormal,SparseArray[Select[ArrayRules[c.c],(#[[1,2]]==#[[1,3]]&&P[alg[#[[1,2]]]]==1)&]/.{i_,j_,j_,k_}:>{i,j,k},Table[Dim[alg],{3}]]-Transpose[Transpose[c,{1,3,2}].s,{1,3,2}],{3}]]

End[];
EndPackage[];
