BeginPackage["SuperLie`Tensor`",
 {"SuperLie`", "SuperLie`Domain`", "SuperLie`Space`"}]

MatrixLieAlgebra::usage =
  "MatrixLieAlgebra[name, vect] - defines \"name\" as a matrix Lie 
(super)algebra on the space \"vect\"; MatrixLieAlgebra[matr, Dim->dim] -
defines \"matr\" as Lie (super)algebra of dim*dim matrices (if
dim={d1,d2,..} - d1 odd components, d2 - even, d3 - odd, ...).";

TensorSpace::usage = 
  "TensorSpace[name,over,{comp,..}] - define space \"name\" as tensor 
product of components. Repeated components may be written as comp^n. All
component must be the relatives of the space \"over\".";

CompList::usage = "CompList[TensSpace] - the list of vector spaces -
 components of tensor space."

Rank::usage = "Rank[tensSpace] - the rank of the tensor space."

Begin["$`"]

(******************  Matrix Lie Algebra *************************)


 MatrixLieAlgebra[g_, vect_?VectorQ, opts___ ] :=
   Module [{i, v, prop, brk },
      prop = UnionKeys[{ Vector, BasisPattern->(_g), TheSpace->vect, opts },
			Options[Algebra], Options[VectorSpace] ];
      SetProperties[g, prop ];
      brk = KeyValue[ prop, Bracket ];
      P[g[i_,j_]] ^:= Mod[P[vect[i]]+P[vect[j]], 2];
      Dim[g] ^= Dim[vect]^2;
      PDim[g] ^= {PDim[vect][[1]]^2 + PDim[vect][[2]]^2,
		2 PDim[vect][[1]] PDim[vect][[2]] };
      g[i_] := g[1+Quotient[i-1,Dim[vect]], 1+Mod[i-1,Dim[vect]]];
      brk[ g[i_,j_], g[k_,l_] ] ^:= VPlus [ Delta[j-k] ~SVTimes~ g[i,l],
		(-Delta[i-l]*(-1)^(P[g[i,j]]*P[g[k,l]])) ~SVTimes~ g[k,j] ];
      For [i=1, i<=8, ++i,
	v = Relatives[vect][[i]];
	If [v===None, Continue[] ];
        Switch[ Mod[i, 4],
	   1,  brk[ g[i_,j_], v[k_] ] ^:= Evaluate[Delta[j-k]~SVTimes~v[i]],
	   2,  brk[ g[i_,j_], v[k_] ] ^:= 
		  Evaluate[(-Delta[k-i]*(-1)^(P[g[i,j]]*P[v[k]]))~SVTimes~v[j]],
	   3,  brk[ g[i_,j_], v[k_] ] ^:= 
		  Evaluate[(-Delta[j-k]*(-1)^P[g[i,j]])~SVTimes~v[i]],
	   4,  brk[ g[i_,j_], v[k_] ] ^:=
		  Evaluate[(-Delta[k-i]*(-1)^(P[g[i,j]]*P[v[j]]))~SVTimes~v[j] ]
      ] ]
  ]

 MatrixLieAlgebra[ name_, opts___ ] :=
   Module [ {vect, covect},
      VectorSpace[vect, opts, CoLeft->covect];
      MatrixLieAlgebra[name, vect]
   ]


(********************************************************
 *   Tensor space is a vector space with multi-indexed basis 
 * t[i1,..], indexes are associated with tensor components - 
 * relative vector spaces
 ********************************************************)


TensorSpace::list = "Argument `` might be list of components."
TensorSpace::comp = "Components might be relatives of the spaces ``."

NewValue[Rank]

TensorSpace[name_, vect_, comp_, opts___] :=
  Module[ { cmp, n, k },
    If [Head[comp]=!=List, Message[TensorSpace::list, comp]; Return[] ];
    Vector[name];
    CompList[name] ^= cmp = Flatten[comp /. x_^i_Integer :> Table[x, {i}] ];
    Rank[name] ^= Length[cmp];
    TheSpace[name] ^= vect;
    If [!VectorQ[vect], Message[TensorSpace::comp, vect]; Return[] ];
    For [n=1, n<=Rank[name], ++n,
       k = Position[ Relatives[vect], cmp[[n]] ];
       If [Length[k]==0, Message[TensorSpace::comp, vect]; Return[] ];
    ];
    P[expr_name] ^:=
	PolynomialMod[Sum[P[ CompList[[j]][expr[[j]]] ], {j,Rank[name]}], 2];
  ]

End[]
EndPackage[]

