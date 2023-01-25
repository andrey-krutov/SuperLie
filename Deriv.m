BeginPackage["SuperLie`Deriv`",
 {"SuperLie`", "SuperLie`Domain`", "SuperLie`Space`"}]

SuperLie`Deriv`Der::usage =
  "Der[form], Der[v**form] is the exterior derivative on forms (with
trivial (scalar) coefficients as well as  or with coefficients in a
module). The \"form\" may be an odd left form an an algebra or an
exterior product of such form; \"v \" must be an element of a module
over the same algebra. The derivative of 0-form is written as
Der0[v,algebra]."

SuperLie`Deriv`Der0::usage =
  "Der0[v,g] is the exterior derivative on 0-forms v**wedge[]
with coefficients in g-module."

SuperLie`Deriv`der::usage = "der - unevaluated form of the exterior derivative Der."

SuperLie`Deriv`ZDer::usage = "ZDer[f] is the exterior derivative of the form f (with
trivial (scalar) coefficients). ZDer[f][x0,x1,...,xn] gives the value
of the derivative of n-form f on elements x0,x1,...,xn. The expression
ZDer[f] may be used in symbolical calculations."

SuperLie`Deriv`ExteriorAlgebra::usage =
"ExteriorAlgebra[name, x, options] defines an exterior algebra on the space x.
Options changes the operation names: Wedge->exterior product, Der->derivative,
CTimes->operation for x\[CenterDot]dx."

SuperLie`Deriv`NDer::usage =
"NDer->opname in an option of ExteriorAlgebra. If gives the name of the 
derivative (normalized form)."

Begin["$`"]

(************* Der - derivative for exterior forms **************)

SetProperties[Der, {Vector, Vector->__, Linear->First} ]
SetProperties[Der0, {Vector, Vector->__, Linear->First} ]

(*
Der[form_Wedge] :=
   Module[{r, range, sg, sm, sumattr},
     range = Length[form];
     sumattr = Attributes[VSum];
     Attributes[VSum] = {OneIdentity};
     For [r=1; sg=1; sm={}, r<=range, ++r,
	 sm = { sm,  (sg ~SVTimes~ 
		(ReplacePart[form, CoAct[form[[r]]], r]//.SymmetricRule[Wedge])) };
	    sg *= (-1)^P[form[[r]]]
     ];
     Attributes[VSum] = sumattr;
     VPlus @@ Flatten[sm]
   ]
*)

Der[form_wedge] :=
   Module[{r, range, sg, sm, sumattr},
     range = Length[form];
     sumattr = Attributes[VSum];
     Attributes[VSum] = {OneIdentity};
     For [r=1; sg=1; sm={}, r<=range, ++r,
	   sm = { sm,  (sg ~SVTimes~ Wedge[Take[form,r-1], Der[form[[r]]], Drop[form,r]])};
	   sg *= (-1)^P[form[[r]]]
     ];
     Attributes[VSum] = sumattr;
     VPlus @@ Flatten[sm]
   ]
   
Der[wPower[f_,k_]] ^:=
  If[DivPowersQ[f,wPower],
     Wedge[Der[f],wPower[f,k-1]],
     SVTimes[k, Wedge[Der[f],wPower[f,k-1]]]];

(* HoldPattern[derAlgebra[Wedge[dg_,___ ]]] := DLeft[Head[dg]] *)
HoldPattern[derAlgebra[wedge[dg_,___ ]]] := derAlgebra[dg]
HoldPattern[derAlgebra[wPower[dg_,_]]] := derAlgebra[dg]
derAlgebra[dg_] := DLeft[Head[dg]]

Der[vect_**form_] :=
   VPlus[
     Der0[vect,derAlgebra[form]] ~ep1~ form,
     SVTimes[(-1)^P[vect], vect**Der[form]]]

Der[vect_] := CoAct[vect];

Der0[vect_,alg_:Auto] :=
   Module[{j, sm={}, sgn, g, dg, m},
     g = If[alg===Auto, TheAlgebra[TheModule[vect]], alg];
     dg = DLeft[g];
     For [ j=1, j<=Dim[g], ++j,
         m = Act[g[j], vect];
       	 If [m==0, Continue[]]; 
         sm = { sm, ((-1)^(P[dg[j]]*(1+P[vect])))~SVTimes~m ** dg[j] } 
    ];
     VPlus @@ Flatten[sm]
   ]

SetProperties[der, {Vector, Vector->__, Linear->First} ]
OpSymbol[Der] ^= der
Operator[der] ^= Der


(*Der[vect_] := Der[Wedge[vect]]*)

SetProperties[ep1, {Vector, Vector->__, Linear->First} ]

ep1[vect_**form1_, form2_] :=
    vect ** ((form1 ~Wedge~ form2) (*//. SymmetricRule[Wedge]*))

(*
Der[vect_**form_Wedge] :=
   Module[{j, sm, g, dg, dform},
     g = TheAlgebra[TheModule[vect]];
     dg = DLeft[g];
     sm = {SVTimes[(-1)^P[vect], vect**Der[form]]}; 
     For [ j=1, j<=Dim[g], ++j,
         m = Act[g[j], vect];
       	 If [m==0, Continue[]]; 
	 dform = Wedge[dg[j], form ] //. SymmetricRule[Wedge];
         If [dform==0, Continue[]];
         sm = { sm, ((-1)^(P[dg[j]]*(1+P[vect])))~SVTimes~ m ** dform } 
    ];
     VPlus @@ Flatten[sm]
   ]

Der[vect_**form_] := Der[vect**Wedge[form]]

Der[vect_] :=
  With[{m=TheModule[vect]},
    If[ TheAlgebra[m] === Relatives[m][[8]], Der[Wedge[vect]], Der0[vect] ]
    /; m=!=None
  ];
*)

(* ===== ZDer === Exterior derivative (symbolic variant) ===== *)

ZDer[f_,opts___][x___] :=
	($DerOp=(Bracket/.{opts})/.Options[ZDer];
		zDerAux[f,x])

Options[ZDer]={Bracket->Act}

SetProperties[zDerAux, {Vector,Vector->_,Linear}]

zDerAux[f_,x___]:=
  Module[{i,j,xi,xj,pxi,pxj,sgi,sgj,r={},a={x},a1,a2,n,y},
	n=Length[a];
	sgi=1;
	For[i=1,i<n,i++,
	  xi=a[[i]];
	  pxi=P[xi];
	  a1=Take[a,i-1];
	  a2=Take[a,i-n];
	  sgj=sgi;
	  For[j=i+1,j<=n,j++,
	  	xj=a[[j]];
		pxj=P[xj];
		y=SVTimes[sgj, $DerOp[xi,xj]];
		sgj *= (-1)^(pxi*pxj);
		If[y=!=0,r={r,f[Sequence@@a1,Sequence@@ReplacePart[a2,y,j-i]]}]];
	  sgi=-sgi];
	VPlus@@Flatten[r]]

(******* ExteriorAlgebra ********)

ExteriorAlgebra[name_, x_, opts___Rule] :=
 With[{Der$l=Der/.{opts},
       NDer$l=NDer/.{opts},
       der$l=der/.{opts},
       tens=CTimes/.{opts}/.CTimes->Tp,
       Wedge$l=Wedge/.{opts},
       n = Dim[x],
       ptrn = BasisPattern[x],
       dx = GetRelative[x,PiRight]},
 With[{dptrn=PolyPattern[Wedge$l,BasisPattern[dx]]},
  Module[ { i , m, pdim=PDim[x] },
   If[v===$Failed, Return[$Failed]];
   If[!VectorQ[Der$l],
     SetProperties[Der$l, {Vector, Vector->__, Linear->First}];
	 P[Der$l] ^= 1];
   If[!VectorQ[tens],
     Attributes[tens] = {OneIdentity};
     SetProperties[tens,
       {Vector, Vector->__, Graded, ZeroArg, DegTimes, Linear->Last}];
     tens[c_?ScalarQ,v_] := SVTimes[c, tens[VTimes[],v]];
     tens[a_,tens[b_,c_]] := tens[VTimes[a,b],c];
     P[tens] ^= 0];
   If[!VectorQ[Wedge$l],
     Attributes[Wedge$l] = { Flat, Listable, OneIdentity };
     SetProperties[Wedge$l, {Vector, Vector->__, Linear, Graded, DegTimes, Symmetric}];
     Format[e:Wedge$l[v_]] := v;
	 MakeBoxes[e:Wedge$l[v_], fmt_] := InterpretationBox[MakeBoxes[v,fmt],e];
     Format[Wedge$l[]] := "I";
	 MakeBoxes[Wedge$l[], fmt_] := InterpretationBox["I", e];
	 P[Wedge$l] ^= 0];
   Wedge$l[a___,tens[cb_,b_],c___] :=
       SVTimes[(-1)^(P[Wedge$l[a]]P[cb]),tens[cb,Wedge$l[a,b,c]]];
   SetProperties[name, {Vector,
		BasisPattern-> tens[_,dptrn],
		TheSpace->x, Dim->Infinity } ];
   NDer$l[f_] := NormDer[Der$l[f], tens];
   Der$l[tens[c_,f_]] := VSum[tens[LDer[c,x[i],x[_]],Wedge$l[dx[i],f]],{i,1,n}];
   Der$l[f:dptrn]:=0;
   Der$l[c_] := Der$l[tens[c,Wedge$l[]]];
   name::usage = SPrint["`` = \[CapitalOmega](``)", name, x]
 ]]]
 

NormDer[expr_, tens_] :=
    (Sort[VExpand[expr],OpOrd[{tens,SVTimes}]] //.
	      LinearCollectRule[tens,First] /. 
	      tens[x_,v_]:>tens[VNormal[x],v] /.
	      HomogenRule[tens,First])

OpOrd[oplist_][f_,g_]:=
 Module[{x=f,y=g},
   While[MemberQ[oplist,Head[x]], x=Last[x]];
   While[MemberQ[oplist,Head[y]], y=Last[y]];
   OrderedQ[{x,y}]]

End[]
EndPackage[]

