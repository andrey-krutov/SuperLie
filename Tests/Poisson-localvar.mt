
VectorSpace[d]

Symmetric[VTimes]

VectorSpace[p,Dim->1]
VectorSpace[q,Dim->1]

CartanMatrixAlgebra[g,{x,h,y},{{2}}]
SubModule[m,g, Basis[x]]

PoissonAlgebra[po,{p,q}]

Print[Pb[f,g]]

Test[
	VNormal[Pb[p[1],q[1]]]
	,
	VTimes[]
	,
	TestID->"l is not defined globallyr" 
]
