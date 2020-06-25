(******************  Vector Lie Algebra *************************)

BeginPackage["SuperLie`Vecfield`",
 {"SuperLie`", "SuperLie`Space`", "SuperLie`Domain`", "SuperLie`Enum`", "SuperLie`Symalg`"}]

SuperLie`Vecfield`VectorLieAlgebra::usage = 
  "VectorLieAlgebra[name, x] defines a Lie (super)algebra \"name\" as the
algebra of vector fields on the space \"x\" and its action on the
(super)space of polynomials on \"x\".";

SuperLie`Vecfield`VectorRepresentation::usage =
  "VectorRepresentation[g, vect] maps algebra g into vector Lie (super)algebra
vect over an g-module." 

SuperLie`Vecfield`Lb::usage = "Lb[x,y] is the Lie bracket (operator)."
SuperLie`Vecfield`lb::usage = "lb[x,y] is the Lie bracket (unevaluated form)."

NewBracket[Lb, Unevaluated->lb, Output->ArgForm["[``,``]"] (*,
	TeX->ArgForm["\\left[``,``\\right]"] *) ]
Jacobi[Lb->{CircleTimes,VTimes}]

SuperLie`Vecfield`Div::usage = "The options Div->operation gives the name the divergention of
(poly)vector fields"

(*Lb[_,Id] ^= 0*)

Begin["$`"]

spm[x_, ct_[y_,v_], ct_] := ct[VTimes[x,y],v]
spm/: HoldPattern[VTimes[x_,spm[y_,v_,ct_]]]:=spm[VTimes[x,y],v,ct]
SetProperties[spm, {Vector, Vector->__, Linear}]
spm[x_, v_, ct_] := ct[x,v]

VectorLieAlgebra[name_, x_, opts___Rule] :=
 With[{Lb$l=Lb/.{opts},
       lb$l=lb/.{opts},
       ct=CTimes/.{opts}/.CTimes->Tp,
	   Div$l=Div/.{opts},
	   Wedge$l=Wedge/.{opts},
           wedge$l=wedge/.{opts},
	   v = GetRelative[x,CoLeft]},
  Module[ { i , dim, pdim=PDim[x], s, y, r},
   If[v===$Failed, Return[$Failed]];
   If[!VectorQ[ct],
     Attributes[ct] = {OneIdentity};
     SetProperties[ct,
       {Vector, Vector->__, Graded, ZeroArg, DegTimes, Linear->Last}];
     ct[c_?ScalarQ,v_] := SVTimes[c, ct[VTimes[],v]];
     ct[a_,ct[b_,c_]] := ct[VTimes[a,b],c];
     P[ct] ^= 0];
   If[!VectorQ[wedge$l],
     Attributes[wedge$l] = { Flat, Listable, OneIdentity };
     SetProperties[wedge$l, {Vector, Vector->__, Linear, Graded, DegTimes, Symmetric}];
     Format[e_wedge/;Length[e]==1] := e[[1]];
     Format[wedge$l[]] := "I";
     P[wedge$l] ^= 0];
   If[!VectorQ[Lb$l],
     NewBracket[Lb$l, Output->ArgForm["[``,``]"] (*, TeX->ArgForm["\\left[``,\\,``\\right]"]*) ];
     Jacobi[Lb$l->{CircleTimes,VTimes,wedge$l}];
	 P[Lb$l] ^= 0;
     Lb$l::usage = SPrint["``[x,y] is the Lie bracket in algebra ``=vect(``).", Lb$l, name, x]];
   If[!VectorQ[Div$l],
     SetProperties[Div$l, {Vector, Vector->First, Linear->First}];
	 P[Div$l]^=0];
   Wedge$l[a___,ct[cb_,b_],c___] :=
       SVTimes[(-1)^(P[Wedge$l[a]]P[cb]),ct[cb,Wedge$l[a,b,c]]];
   If [pdim[[1]]===0,
      dim = 2^(pdim[[2]]-1); pdim = (dim|dim),
    (*else*)
      pdim = If[pdim[[2]]===0, Infinity, (Infinity|Infinity)]
   ];
   SetProperties[name, {Vector,
		BasisPattern-> ct[_,v[_]],
		TheSpace->x, Bracket->Lb$l, bracket->lb$l, Dim->dim } ];
   Lb$l[l_v, r_x] := ScalarProduct[l, r]~SVTimes~VTimes[];
   Off[Part::pspec];
   For [i=1, i<=8, ++i,
    With[{m = Relatives[x][[i]]},
     If [m===None, Continue[] ];
     Switch[ Mod[i,4],
	1,  Lb$l[ ct[x[i_],v[j_]], m[k_] ] := Evaluate[ Delta[j-k]~SVTimes~m[i] ],
	2,  Lb$l[ ct[x[i_],v[j_]], m[k_] ] :=	
	  Evaluate[(-Delta[k-i]*(-1)^((P[x[i]]+P[v[j]])*P[x[k]]))~SVTimes~m[j]],
	3,  Lb$l[ ct[x[i_],v[j_]], m[k_] ] :=
		Evaluate[(Delta[j-k]*(-1)^(P[x[i]]+P[v[j]]))~SVTimes~m[i] ],
	0,  Lb$l[ ct[x[i_],v[j_]], m[k_] ] :=
	  Evaluate[(-Delta[k-i]*(-1)^((P[x[i]]+P[v[j]])*P[m[k]]))~SVTimes~m[j] ]
      ] ] ];
     On[Part::pspec];
     Lb$l[ ct[f_:VTimes[],z_v], ct[g_:VTimes[],m_v]] :=
        VPlus[ (f~VTimes~Lb$l[z,g]) ~ct~ m, 
	           (-(-1)^((P[f]+P[z])*(P[g]+P[m]))) ~SVTimes~ (g ~VTimes~ Lb$l[m, f]) ~ct~ z];
     Lb$l /: Squaring[ ct[f_:VTimes[],z_v], Lb$l] := VIf[Mod[P[f]+P[z],2]==1, (f~VTimes~Lb$l[z,f]) ~ct~ z];
(*     Lb$l[ ct[f_:VTimes[],z_v], ct[g_:VTimes[],m_v]] := *)
     Lb$l[ ct[f_:VTimes[],z_v], ct[g_,m_]] :=
        VPlus[ (f ~VTimes~ Lb$l[z,g]) ~ct~ m,
		((-1)^((P[f]+P[z])P[g])) ~SVTimes~ spm[g,Lb$l[ct[f,z], m],ct] ]; 
    Lb$l[ ct[f_:VTimes[],z_v], m_x] := VTimes[f,Lb$l[z,m]];  (* added 000305 *)
    Lb$l[ ct[f_:VTimes[],z_v], m_?VectorQ] :=
	VSum[((-1)^((P[f]-P[x[i]])*P[x[i]])) ~SVTimes~ ct[LDer[f,x[i],x[_]], Lb$l[ct[x[i],z], m]],
	  {i, Dim[x]} ] /; MemberQ[Relatives[x],Head[m]];
	 Div$l[ct[f_:VTimes[],v[i_]]]:=SVTimes[(-1)^(P[x[i]]P[f]),LDer[f,x[i],x[_]]];
	 Div$l[ct[f_:VTimes[],z:wedge$l[___v]]]:=
	   (s=1;VSum[y=z[[i]];
	             r=SVTimes[s,ct[LDer[f,y/.v->x,x[_]], Drop[z,{i}]]];
            	 s = s*(-1)^(P[y]);
				 r, {i,1,Length[z]}]);
    (* 011102: added enumeration and Basis[g, d] *)
     If[ KeyValue[{opts}, Enum] =!= False,
	   EnumSet[name,  { -1, Infinity, 1 } -> { d_ :> Flatten[Outer[ct, DegreeBasis[d+1,Basis[x]], Basis[v]]]}]];
     name/: ReGrade[name, 0] := (ReGrade[x, Homogen]; ReGrade[name]);
     name/: ReGrade[name, gr_Integer] := ReGrade[name, vectReGList[Basis[x],gr]]/; -PDim[x][[2]]<=gr<=PDim[x][[2]];
     ReGrade[name, gr_] ^:= (ReGrade[x, Parity]; ReGrade[name])/; gr==PDim[x][[2]];
     ReGrade[name, glist_] ^:= (ReGrade[x, glist]; ReGrade[name])/; !NumberQ[glist];
     ReGrade[name] ^:= calcVfBasis[name, x, ct, VTimes];
     If[ListQ[GList[x]], ReGrade[name], ReGrade[name,0]];
     name::usage = SPrint["`` = vect(``)", name, x]
    ]
 ]


vectReGList[basis_, no_] := Module[{j=no}, Table[If[P[basis[[i]]]==1 && j>0, j--; 0, (*else*) 1], {i,Length[basis]}]] 

vectReGList[basis_, no_] := Module[{j=-no}, 
  Reverse[Table[If[P[basis[[i]]]==1 && j>0, j--; 0, (*else*) 1], {i,Length[basis],1,-1}]]] /; no<0

vfBasis[x_, dx_, ct_, vt_, d_, min_, max_] :=
  Flatten[Table[Outer[ct, GradeBasis[d - i, Basis[x], vt], Basis[dx, i]], {i, min, max}]]

calcVfBasis[g_, x_, ct_, vt_] :=
  Module[{d = Dim[x], b, i, gi, g0 = Infinity, g1 = -Infinity},
    If[! IntegerQ[d] || d <= 0, Return[$Failed]];
    b = Basis[x];
    For[i = 1, i <= d, i++,
      gi = Grade[x[i]];
      If[! IntegerQ[gi] || gi < 0 || gi == 0 && P[x[i]] =!= 1, 
        Return[$Failed]];
      g0 = Min[g0, gi];
      g1 = Max[g1, gi]];
    With[{dx = CoLeft[x], min = -g1, max = -g0},
      Basis[g, k_] ^:= vfBasis[x, dx, ct, vt, k, min, max]]]


VectorRepresentation::ndef =
 "`` should be defined as vector Lie (super)algebra"

VectorRepresentation[g_, v_, opts___Rule] :=
  Module[{m, dm, img, bg, bm, mdim, brk},
    m = TheSpace[v];
    If[!SymbolQ[m] ||
       !SymbolQ[dm = CoLeft[m]],
      Message[VectorRepresentation::ndef, v];
      Return[$Failed]];
    bg = Basis[g];
    bm = Basis[m];
    mdim = Length[bm];
    brk = Bracket[g];
    Image[g] ^= img =
      Table[VSum[brk[bg[[i]],bm[[j]]]**dm[j],{j,1,mdim}],{i,1,Dim[g]}];
    InSpace[g]^=v;
	DefMapping[Mapping/.{opts}, g, img];
  ]

DPrint[1, "SuperLie`Vecfield` loaded"]

End[]
EndPackage[]


