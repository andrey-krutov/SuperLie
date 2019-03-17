(* === qAlgebra ========================= *)
(* The algebras q, sq, psq --- *)

(* TO DO: p...Algebra for $p>0 *)

BeginPackage["SuperLie`Q`", {"SuperLie`", "SuperLie`Domain`", "SuperLie`Enum`", "SuperLie`Gl`", "SuperLie`Space`"}]

SuperLie`Q`qAlgebra::usage = "qAlgebra[g,{x,y},n] define the superalgebra g = q(n)
 with basis x[i,j] (even elements) and y[i,j] (odd elements)."

SuperLie`Q`sqAlgebra::usage = "sqAlgebra[g,{x,y},n] define the superalgebra g = sq(n)
 with basis x[i,j] (even elements) and y[i], y[i,j] (odd elements)."

SuperLie`Q`pqAlgebra::usage = "pqAlgebra[g,{x,y},n] define the superalgebra g = pq(n)
 with basis x[i], x[i,j] (even elements) and y[i,j] (odd elements)."

SuperLie`Q`psqAlgebra::usage = "psqAlgebra[g,{x,y},n] define the superalgebra g = psq(n)
 with basis x[i], x[i,j] (even elements) and y[i], y[i,j] (odd elements)."

SuperLie`Q`q2Algebra::usage = "q2Algebra[g, n] defines the superalgebra g = q^2(n)
 with basis \!\(\(g\_ij\) \[Tau]\^k=g[i,j][k]\)."

SuperLie`Q`psq2Algebra::usage = "psq2Algebra[g, n] defines the superalgebra g = psq^2(n)
 with basis \!\(\(g\_i\) \[Tau]\^k=g[i][t]\), \!\(\(g\_ij\) \[Tau]\^k=g[i,j][t]\)."

SuperLie`Q`psl2pAlgebra::usage =
  "psl2pAlgebra[g, {a,b}, n] - defines the superalgebra
   g = \!\(\"\[GothicP]\[GothicS]\[GothicL](n|n)\"\_\[Pi]\%(2)\)
   with basis \!\(a\_\(i,j\)[k]\) and \!\(b\_\(i,j\)[k]\)."

Begin["$`"]

qAlgebra[g_, {x_,y_}, dim_, opts___] :=
  Module [{i, v, prop, brk, eset},
      prop = Sequence@@UnionKeys[{opts}, Options[Algebra], Options[VectorSpace]];
      glAlgebra[x, Dim->dim, prop];
      Define[y, {Vector, prop}];
      P[_y] ^= 1;
      With[{brk = KeyValue[ {prop}, Bracket ]},
	brk[u_y,v_x] ^:= (-1)~SVTimes~brk[v,u];
	brk[ x[i_,j_], y[k_,l_] ] ^:=
	  VIf[j==k, y[i,l]] ~VPlus~ VIf[i==l, (-1)~SVTimes~y[k,j]];
	brk[ y[i_,j_], y[k_,l_] ] ^:=
	  VIf[j==k, x[i,l]] ~VPlus~ VIf[i==l, x[k,j]];
        y/: Squaring[y[i_,j_],brk] := VIf[i==j, x[i,j]]];
      Grade[y[i__]] ^:= Grade[x[i]];
      Weight[y[i__]] ^:= Weight[x[i]];
      Define[g, {Vector, BasisPattern->(_x|_y)}];
      SetProperties[g, {prop}];
      emode = KeyValue[{prop}, Enum];
      If[ emode =!= False,
	EnumSet[y,  { 0, 0, 1 } -> { 0 :> Table[y[i,i], {i, dim}] },
		{ 1, dim-1, 1 } -> { deg_ :> Table[ y[i,i+deg], {i, dim-deg}] },
		{-1,-dim+1,-1 } -> { deg_ :> Table[ y[i-deg,i], {i, dim+deg}] }
	];
 	EnumJoin[g, x, y]
      ];
      Dim[g] ^= 2dim^2;
      PDim[g] ^= {dim^2, dim^2};
      Components[g] ^= {{x, 2, {{#1,1,dim},{#2,1,dim}}&, True&},
			{y, 2, {{#1,1,dim},{#2,1,dim}}&, True&}};
      BracketMode[g] ^= Regular;
      g::usage = SPrint["`` = q(``)", g, dim ]
  ]


sqAlgebra[g_, {x_,y_}, dim_, opts___] :=
  Module [{i, v, prop, brk, emode, zn },
      prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace]];
      glAlgebra[x, Dim->dim, opts];
      Define[y, {Vector, prop}];
      P[_y] ^= 1;
      With[{brk = KeyValue[ prop, Bracket ]},
	brk[u_y,v_x] ^:= (-1)~SVTimes~brk[v,u];
      	brk[ x[i_,j_], y[k_,l_] ] ^:= 
	  VPlus [ VIf [ j==k && i!=l, y[i,l] ],
	   	  VIf [ i==l && j!=k, (-1) ~SVTimes~ y[k,j] ],
		  VIf [ j==k && i==l, VSum[y[i$$], {i$$, i->j}] ] ];
	brk[ x[i_,j_], y[k_] ] ^:=
	  VPlus [ VIf [ j==k && i!=j, y[i,j] ],
	  	  VIf [ j==k+1 && i!=j, (-1) ~SVTimes~ y[i,j] ],
		  VIf [ i==k && i!=j, (-1) ~SVTimes~ y[i,j] ],
	  	  VIf [ i==k+1 && i!=j, y[i,j] ] ];
      	brk[ y[i_,j_], y[k_,l_] ] ^:=
	  VIf[j==k, x[i,l]] ~VPlus~ VIf[i==l, x[k,j]];
      	brk[ y[i_,j_], y[k_] ] ^:=
	  VPlus [ VIf [ j==k, x[i,j] ],
		  VIf [ j==k+1, (-1) ~SVTimes~ x[i,j] ],
		  VIf [ i==k, x[i,j] ],
		  VIf [ i==k+1, (-1) ~SVTimes~ x[i,j] ] ];
     	brk[y[i_], y[j_]] ^:=
	  VPlus [ VIf [i==j, SVTimes[2,x[i,i]]~VPlus~SVTimes[2,x[i+1,i+1]] ],
		  VIf [i==j+1, SVTimes[-2,x[i,i]] ],
		  VIf [i==j-1, SVTimes[-2,x[j,j]] ] ];
        brk[y[i_], y[j_,k_]] ^:= brk[y[j,k],y[i]];
        y/: Squaring[y[i_,j_],brk] = 0;
        y/: Squaring[y[i_],brk] := x[i,i]~VPlus~x[i+1,i+1] ];
      Grade[y[i_,j_]] ^:= Grade[x[i,j]];
      Grade[y[i_]] ^:= 0;
      Weight[y[i_,j_]] ^:= Weight[x[i,j]];
      Weight[y[i_]] ^= Table[0,{dim}];
      Define[g, {Vector, BasisPattern->(_x|_y)}];
      SetProperties[g, prop];
      emode = KeyValue[prop, Enum];
      If[ emode =!= False,
	EnumSet[y,  { 0, 0, 1 } -> { 0 :> Array[y, dim-1] },
		{ 1, dim-1, 1 } -> { deg_ :> Table[ y[i,i+deg], {i, dim-deg}] },
		{-1,-dim+1,-1 } -> { deg_ :> Table[ y[i-deg,i], {i, dim+deg}] }
	];
	EnumJoin[g, x, y]
      ];
      Dim[g] ^= 2dim^2-1;
      PDim[g] ^= {dim^2, dim^2-1};
      Components[g] ^= {{x, 2, {{#1,1,dim},{#2,1,dim}}&, True&},
			{y, 2, {{#1,1,dim},{#2,1,dim}}&, (#1!=#2)&},
			{y, 1, {{#,1,dim-1}}, True& }};
      BracketMode[g] ^= Regular;
      TheAlgebra[g] ^= g;
      g::usage = SPrint["`` = sq(``)", g, dim ]
  ]



psqPrj[g_, j_, m_] :=
 VSum[(-k/m) ~SVTimes~ g[k], {k, 1, j-1}] ~VPlus~
	VSum[((m-k)/m) ~SVTimes~ g[k], {k, j, m-1}]
	
	
SetProperties[pqEmb, {Vector,Vector->First,Linear->First}];
	
pqEmb[x_[i_],x_,y_]:=VPlus[y[i,i],SVTimes[-1,y[i+1,i+1]]]
pqEmb[x_[i_,j_],x_,y_]:=y[i,j]

antiCom[g_[i_,j_], g_[k_,l_], g_] :=  VIf[j==k, g[i,l]] ~VPlus~ VIf[i==l, g[k,j]];
SetProperties[antiCom,{Vector,Vector->_,Linear}]

pqAlgebra[g_, {x_,y_}, dim_, opts___] :=
  Module [{i, v, prop, brk, emode, zn, yBrk, x2y },
      prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace]];
      NewBracket[yBrk];
      slAlgebra[x, Dim->dim, opts];
      glAlgebra[y, Dim->{0,dim}, Bracket->yBrk, opts];
      With[{brk = KeyValue[ prop, Bracket ]},
	brk[u_x, y[i__]] ^:= pqEmb[brk[u,x[i]],x,y];
      	brk[y[i__], u_x] ^:= pqEmb[brk[x[i],u],x,y];
	brk[ y[i_,j_], y[j_,i_] ] ^:= VPlus[psqPrj[x,i,dim], psqPrj[x,j,dim]];
      	brk[ y[i_,j_], y[j_,l_] ] ^:= x[i,l] /; i!=l;
      	brk[ y[i_,j_], y[k_,i_] ] ^:= x[k,j] /; j!=k;
      	brk[ y[i_,j_], y[k_,l_] ] ^:= 0 /; (i!=l && j!=k);
        antiBrk[u_x, v_y] ^:= antiCom[pqEmb[u,x,y],v,y];
        antiBrk[u_y, v_x] ^:= antiCom[u,pqEmb[v,x,y],y];
        antiBrk[u_y, v_y] ^:= brk[x@@u,x@@v];
     ];
      Define[g, {Vector, BasisPattern->(_x|_y)}];
      SetProperties[g, prop];
      emode = KeyValue[prop, Enum];
      If[ emode =!= False,
	EnumJoin[g, x, y]
      ];
      Dim[g] ^= 2dim^2-1;
      PDim[g] ^= {dim^2-1, dim^2};
      TheAlgebra[g] ^= g;
      g::usage = SPrint["`` = pq(``)", g, dim ]
  ]



psqAlgebra[g_, {x_,y_}, dim_, opts___] :=
  Module [{i, v, prop, brk, emode, zn },
      prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace]];
      slAlgebra[x, Dim->dim, opts];
      Define[y, {Vector, opts}];
      P[_y] ^= 1;
      With[{brk = KeyValue[ prop, Bracket ]},
	brk[u_x, y[i__]] ^:= brk[u,x[i]]/.x->y;
      	brk[y[i__], u_x] ^:= brk[x[i],u]/.x->y;
      	brk[x[i_,j_], y[j_,i_]] ^:= VSum[ y[k], {k, i, j-1}] /; i<j;
	brk[ y[i_,j_], y[j_,i_] ] ^:= VPlus[psqPrj[x,i,dim], psqPrj[x,j,dim]];
      	brk[ y[i_,j_], y[j_,l_] ] ^:= x[i,l] /; i!=l;
      	brk[ y[i_,j_], y[k_,i_] ] ^:= x[k,j] /; j!=k;
      	brk[ y[i_,j_], y[k_,l_] ] ^:= 0 /; (i!=l && j!=k);
      	brk[y[i_,j_], y[k_]] ^:=
	  (Abs[#[[k]]]-Abs[#[[k+1]]])& @ Weight[x[i,j]] ~SVTimes~ x[i,j];
      	brk[y[k_], y[l_]] ^:= 0 /; k!=l && k!=l+1 && k+1!=l;
     	brk[y[k_], y[k_]] ^:= 2~SVTimes~(psqPrj[x,k,dim]~VPlus~psqPrj[x,k+1,dim]);
      	brk[y[k_], y[l_]] ^:= SVTimes[-2,psqPrj[x,l,dim]] /; l==k+1;
      	brk[y[k_], y[l_]] ^:= SVTimes[-2,psqPrj[x,k,dim]] /; l+1==k;
      	brk[y[i_], y[j_,k_]] ^:= brk[y[j,k],y[i]]];
      Grade[y[i_,j_]] ^:= Grade[x[i,j]];
      Grade[y[i_]] ^:= 0;
      Weight[y[i_,j_]] ^:= Weight[x[i,j]];
      Weight[y[i_]] ^= Table[0,{dim}];
      Define[g, {Vector, BasisPattern->(_x|_y)}];
      SetProperties[g, prop];
      emode = KeyValue[prop, Enum];
      If[ emode =!= False,
	EnumSet[y,  { 0, 0, 1 } -> { 0 :> Array[y, dim-1] },
		{ 1, dim-1, 1 } -> { deg_ :> Table[ y[i,i+deg], {i, dim-deg}] },
		{-1,-dim+1,-1 } -> { deg_ :> Table[ y[i-deg,i], {i, dim+deg}] }
	];
	EnumJoin[g, x, y]
      ];
      Dim[g] ^= 2dim^2-2;
      PDim[g] ^= {dim^2-1, dim^2-1};
      TheAlgebra[g] ^= g;
      g::usage = SPrint["`` = psq(``)", g, dim ]
  ]

SetProperties[auxInd, {Vector,Vector->First,Linear->First}]
auxInd[expr_,ind_] := expr[ind]
auxInd[expr_,0] := expr


q2Algebra[g_, dim_, opts___] :=
  Module [{prop, brk, emode, zn, x, y, z, g1},
      prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace],
			{BasisPattern->(g[__][_])|(g[__])} ];
    With[{ brk = KeyValue[ prop, Bracket]},
      qAlgebra[g1,{g,y}, dim, Bracket->brk];
      glAlgebra[g,Dim->dim,opts];
      SetProperties[g, prop];
      g/: g[i_,j_][0] := g[i,j];
      P[g[__][d_]] ^:= Mod[d,2];
      brk = KeyValue[ prop, Bracket ];
      brk[g[i__][q_], g[j__][r_]] ^:= auxInd[brk[g[i],g[j]],q+r] /; (EvenQ[q] || EvenQ[r]);
      brk[g[i__][q_], g[j__][r_]] ^:= auxInd[brk[y[i],y[j]],q+r] /; OddQ[q] && OddQ[r];
      brk[g[i__], g[j__][r_]] ^:= auxInd[brk[g[i],g[j]],r];
      brk[g[i__][r_], g[j__]] ^:= auxInd[brk[g[i],g[j]],r];
      g/: Squaring[g[i__][q_],brk] := auxInd[Squaring[y[i],brk],2*q] /; OddQ[q];
      Weight[g[i__][_]] ^:= Weight[g[i]];
      emode = KeyValue[prop, Enum];
      Switch[ emode,
       Auto,
        Grade[g[__][d_]] ^:= d;
        Grade[g[__]] ^:= 0;
	EnumSet[g,  { 0, 0, 1 } -> { 0 :> Flatten[Array[g, {dim,dim}]] },
	   {1,Infinity,1}->{deg_:>Flatten[ { Table[g[i,i][deg],{i,dim}],
		Table[{g[i,j][deg],g[j,i][deg]},{i,2,dim},{j,1,i-1}] } ] },
	   {-1,-Infinity,-1}->{deg_:>Flatten[ { Table[g[i,i][deg],{i,dim}],
		Table[{g[i,j][deg],g[j,i][deg]},{i,2,dim},{j,1,i-1}] } ] }
	],
       1,
        Grade[g[i_,j_][d_]] ^:= -i+j+d;
        Grade[g[i_,j_]] ^:= -i+j;
	EnumSet[g,
	   {0, 0, 1}-> { 0 :> Flatten[ 
	     {  Table[g[i,i], {i,dim}], 
		Table[ g[i,i+k][-k], {k, 1, dim-1}, {i, dim-k}],
		Table[ g[i+k,i][k], {k, 1, dim-1}, {i, dim-k}]  } ] },
	   {1, Infinity, 1} -> { d_ :>Flatten[
	     {  Table[ g[i,i][d], {i,dim}], 
		Table[ g[i,i+k][d-k], {k, 1, dim-1}, {i, dim-k}],
		Table[ g[i+k,i][d+k], {k, 1, dim-1}, {i, dim-k}] } ] },
	   {-1, -Infinity, -1} -> { d_ :>Flatten[
	     {  Table[ g[i,i][d], {i,dim}], 
		Table[ g[i,i+k][d-k], {k, 1, dim-1}, {i, dim-k}],
		Table[ g[i+k,i][d+k], {k, 1, dim-1}, {i, dim-k}] } ] }
	 ],
       3,
        Grade[g[i_,j_][d_]] ^:= -i+j+d*dim;
        Grade[g[i_,j_]] ^:= -i+j;
	EnumSet[g,
	   {0, 0, 1}-> { 0 :> Table[g[i,i], {i,dim}] },
	   {dim, Infinity, dim} -> { d_ :> Table[g[i,i][d/dim], {i,dim}] },
	   {-dim, -Infinity, -dim} -> { d_ :> Table[g[i,i][d/dim], {i,dim}] },
	   Sequence @@ Table[ {k, Infinity, dim} -> { d_ :>
		Evaluate[ Join[ Table[ g[i,i+k][(d-k)/dim],{i, dim-k}],
		    Table[g[i+dim-k,i][(d-k)/dim+1], {i,1,k}]]] }, {k,dim-1} ],
	   Sequence @@ Table[ {-k, -Infinity, -dim} -> { d_ :>
		Evaluate[ Join[ Table[ g[i+k,i][(d+k)/dim],{i, dim-k}],
		    Table[g[i,i+dim-k][(d+k)/dim-1], {i,1,k}]]] }, {k,dim-1}  ]
        ]
      ];
      Dim[g] ^= Infinity;
      PDim[g] ^= {Infinity,Infinity};
      Dim[g,d_] ^:= dim^2;
      PDim[g] ^= {Infinity,Infinity};
      PDim[g,d_] ^:= {dim^2, 0} /; EvenQ[d];
      PDim[g,d_] ^:= {0, dim^2} /; OddQ[d];
      g::usage = SPrint["`` = q(``)^(2)", g, dim ]
  ]]


psq2Algebra[g_, dim_, opts___] :=
  Module [{prop, brk, emode, zn, x, y, z },
      prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace],
			{BasisPattern->(g[__][_])|(g[__])} ];
      brk = KeyValue[ prop, Bracket ];
      psqAlgebra[g1,{x,y}, dim, Bracket->brk];
      sqAlgebra[g2,{g,z}, dim, Bracket->brk];
      glAlgebra[g, Dim->dim, opts];
      SetProperties[g, prop];
      g/: g[i_,j_][0] := g[i,j];
      g/: g[i_][0] := g[i,i] ~VPlus~ SVTimes[-1,g[i+1,i+1]];
      P[g[__][d_]] ^:= Mod[d,2];
      brk = KeyValue[ prop, Bracket ];
      brk[g[i__][q_], g[j__][r_]] ^:= (brk[x[i],x[j]] /. x[k__]:>g[k][q+r])/;
				(EvenQ[q] || EvenQ[r]);
      brk[g[i__][q_], g[j__][r_]] ^:= (brk[y[i],y[j]] /. x[k__]:>g[k][q+r])/;
				q+r!=0 && OddQ[q] && OddQ[r];
      brk[g[i__][q_], g[j__][r_]] ^:= brk[z[i],z[j]] /; q+r==0 && OddQ[q];
      brk[g[i__], g[j__][r_]] ^:= brk[g[i],z[j]] /. z[k__]:>g[k][r];
      brk[g[i__][r_], g[j__]] ^:= brk[z[i],g[j]] /. z[k__]:>g[k][r];
      Weight[g[i__][_]] ^:= Weight[g[i]];
      Weight[g[i_]] ^:= Evaluate[Table[0, {dim}]];
      emode = KeyValue[prop, Enum];
      Switch[ emode,
       Auto,
        Grade[g[__][d_]] ^:= d;
        Grade[g[__]] ^:= 0;
	EnumSet[g,  { 0, 0, 1 } -> { 0 :> Flatten[Array[g, {dim,dim}]] },
	   {1,Infinity,1}->{deg_:>Flatten[ { Table[g[i][deg],{i,dim-1}],
		Table[{g[i,j][deg],g[j,i][deg]},{i,2,dim},{j,1,i-1}] } ] },
	   {-1,-Infinity,-1}->{deg_:>Flatten[ { Table[g[i][deg],{i,dim-1}],
		Table[{g[i,j][deg],g[j,i][deg]},{i,2,dim},{j,1,i-1}] } ] }
	],
       1,
        Grade[g[i_,j_][d_]] ^:= -i+j+d;
        Grade[g[i_][d_]] ^:= d;
        Grade[g[i_,j_]] ^:= -i+j;
	EnumSet[g,
	   {0, 0, 1}-> { 0 :> Flatten[ 
	     {  Table[g[i,i], {i,dim}], 
		Table[ g[i,i+k][-k], {k, 1, dim-1}, {i, dim-k}],
		Table[ g[i+k,i][k], {k, 1, dim-1}, {i, dim-k}]  } ] },
	   {1, Infinity, 1} -> { d_ :>Flatten[
	     {  Table[ g[i][d], {i,dim-1}], 
		Table[ g[i,i+k][d-k], {k, 1, dim-1}, {i, dim-k}],
		Table[ g[i+k,i][d+k], {k, 1, dim-1}, {i, dim-k}] } ] },
	   {-1, -Infinity, -1} -> { d_ :>Flatten[
	     {  Table[ g[i][d], {i,dim-1}], 
		Table[ g[i,i+k][d-k], {k, 1, dim-1}, {i, dim-k}],
		Table[ g[i+k,i][d+k], {k, 1, dim-1}, {i, dim-k}] } ] }
	 ],
        3,
        Grade[g[i_,j_][d_]] ^:= -i+j+d*dim;
        Grade[g[i_][d_]] ^:= d*dim;
        Grade[g[i_,j_]] ^:= -i+j;
	EnumSet[g,
	   {0, 0, 1}-> { 0 :> Table[g[i,i], {i,dim}] },
	   {dim, Infinity, dim} -> { d_ :> Table[g[i][d/dim], {i,dim-1}] },
	   {-dim, -Infinity, -dim} -> { d_ :> Table[g[i][d/dim], {i,dim-1}] },
	   Sequence @@ Table[ {k, Infinity, dim} -> { d_ :>
		Evaluate[ Join[ Table[ g[i,i+k][(d-k)/dim],{i, dim-k}],
		    Table[g[i+dim-k,i][(d-k)/dim+1], {i,1,k}]]] }, {k,dim-1} ],
	   Sequence @@ Table[ {-k, -Infinity, -dim} -> { d_ :>
		Evaluate[ Join[ Table[ g[i+k,i][(d+k)/dim],{i, dim-k}],
		    Table[g[i,i+dim-k][(d+k)/dim-1], {i,1,k}]]] }, {k,dim-1}  ]
        ]
      ];
      Dim[g] ^= Infinity;
      PDim[g] ^= {Infinity,Infinity};
      Dim[g,d_] ^:= dim^2-1 /; d!=0;
      g/: Dim[g,0] = dim^2;
      PDim[g] ^= {Infinity,Infinity};
      PDim[g,d_] ^:= {dim^2-1, 0} /; EvenQ[d] && d!=0;
      g/: PDim[g,0] = {dim^2, 0};
      PDim[g,d_] ^:= {0, dim^2-1} /; OddQ[d];
      g::usage = SPrint["`` = psq(``)^(2)", g, dim ]
  ]


psl2pAlgebra[g_, {x_,y_}, dim_] :=
  Module [{prop, brk, emode, zn, z },
      prop = UnionKeys[{opts}, Options[Algebra], Options[VectorSpace],
			{BasisPattern->(a[__])|(b[__])|(a[__][_])|(b[__][_])} ];
      brk = KeyValue[ prop, Bracket ];
      pqAlgebra[g1,{x,y}, dim, Bracket->brk];
      glAlgebra[g, Dim->dim, opts];
      SetProperties[g, prop];
      With[{brk = KeyValue[ prop, Bracket ]},
	brk[(u:_x)[i_], (v:_x)[j_]] ^:= brk[u,v][i+j];
	brk[(u:_x)[i_], (v:_y)[j_]] ^:= If[EvenQ[i],brk[u,v],antiBrk[u,v]][i+j];
	brk[(u:_y)[i_], (v:_x)[j_]] ^:= If[EvenQ[j],brk[u,v],SVTimes[-1,antiBrk[u,v]]][i+j];
	brk[(u:_y)[i_], (v:_y)[j_]] ^:=
	 If[EvenQ[i],
	   If[EvenQ[j], brk[u,v], SVTimes[-1,antiBrk[u,v]]],
	   If[EvenQ[j], antiBrk[u,v], SVTimes[-1,brk[u,v]]]][i+j];
	brk[u:_x, (v:_x)[j_]] ^:= brk[u,v][j];
	brk[u:_x, (v:_y)[j_]] ^:= brk[u,v][j];
	brk[u:_y, (v:_x)[j_]] ^:= If[EvenQ[j],brk[u,v],SVTimes[-1,antiBrk[u,v]]][j];
	brk[u:_y, (v:_y)[j_]] ^:= If[EvenQ[j], brk[u,v], SVTimes[-1,antiBrk[u,v]]][j];
 	brk[(u:_x)[i_], v:_x] ^:= brk[u,v][i];
	brk[(u:_x)[i_], v:_y] ^:= If[EvenQ[i], brk[u,v], antiBrk[u,v]][i];
	brk[(u:_y)[i_], v:_x] ^:= brk[u,v][i];
	brk[(u:_y)[i_], v:_y] ^:= If[EvenQ[i], brk[u,v], antiBrk[u,v]][i]
      ];
      x/: x[i__][0] := x[i];
      y/: y[i__][0] := y[i];
      P[x[__][d_]] ^:= 0;
      P[y[__][d_]] ^:= 0;
      Dim[g] ^= Infinity;
      PDim[g] ^= {Infinity,Infinity};
      Dim[g,d_] ^:= 2*dim^2-1;
      PDim[g,d_] ^:= {dim^2-1, dim^2};
      g::usage = SPrint["`` = \!\(\"\[GothicP]\[GothicS]\[GothicL](``|``)\"\_\[Pi]\%(2)\)",
       g, dim, dim ]
] 

(*
Format[g[i_][d_],TeXForm] := StringForm["x_``(``)",i,d]/;EvenQ[d]
Format[g[i_][d_],TeXForm] := StringForm["\\tilde{x}_``(``)",i,d]/;OddQ[d]
Format[g[i__],TeXForm] := Subscripted[x[i]]
Format[g[i_,j_][d_],TeXForm] := 
		StringForm["\\tilde{x}_{````}(``)",i,j,d]/;OddQ[d]
Format[g[i_,j_][d_],TeXForm] := 
	StringForm["x_{````}(``)",i,j,d]/;EvenQ[d]

Format[r_Rational * s__] := HoldForm[r] Times[s]
Format[r_Rational * s__, TeXForm] := HoldForm[r] Times[s]

*)

End[]
EndPackage[]
