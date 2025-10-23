Symmetric[VTimes]

upToDegree = 3

VectorSpace[x, Dim->{1,1}, DLeft->d]

SchoutenAlgebra[sch, {x,d}]

Fbasis = UpToDegreeBasis[3, Join[Basis[x], Basis[d]]]

resAnti = DeleteDuplicates[
 Flatten[Table[
   VNormal[Bb[xx, yy] ~VPlus~ SVTimes[(-1)^((P[xx] + 1) (P[yy] + 1)), Bb[yy, xx]]] === 0, {xx, Fbasis},  {yy, Fbasis}
   ]]]

Test[
	resAnti
	,
	{True}
	,
	TestID->"SchoutenAlgebra: anitcommutativity"
]

resJacobi = DeleteDuplicates[
 Flatten[Table[
   VNormal[
   	Bb[xx, Bb[yy,zz]] ~VPlus~ SVTimes[-1, Bb[Bb[xx,yy],zz]]
   	~ VPlus~ SVTimes[-(-1)^((P[xx]+1)(P[yy]+1)), Bb[yy,Bb[xx,zz]]] 
   	] === 0,
   	 {xx, Fbasis},  {yy, Fbasis}, {zz, Fbasis}
   ]]]

Test[
	resJacobi
	,
	{True}
	,
	TestID->"SchoutenAlgebra: Jacobi"
]

resDer = DeleteDuplicates[
 Flatten[Table[
   VNormal[
   	Bb[xx, VTimes[yy,zz]] ~VPlus~ SVTimes[-1, VTimes[Bb[xx,yy],zz]]
   	~ VPlus~ SVTimes[-(-1)^((P[xx])(P[yy]+1)), VTimes[yy,Bb[xx,zz]]] 
   	] === 0,
   	 {xx, Fbasis},  {yy, Fbasis}, {zz, Fbasis}
   ]]]

Test[
	resJacobi
	,
	{True}
	,
	TestID->"SchoutenAlgebra: Derivation"
]
