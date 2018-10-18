newPackage(
     "ToricSecants",
     Version => "0.1",
     Date => "October 8, 2018",
     Headline => "compute dimensions of secants of toric varieties",
     --HomePage => "",
     Authors => {
	  {Name => "Robert Krone", Email => "rckrone@gmail.com"}
	  },
     PackageImports => {
	  },
     PackageExports => {
	  "NormalToricVarieties",
	  "Matroids"
	  },
     -- DebuggingMode should be true while developing a package,
     --   but false after it is done
     DebuggingMode => true
     )

export {
    "aMatrix",
    "imageMonomials",
    "homogenizeAmatrix",
    "secant",
    "joinIdeal",
    "toricSecantDim",
    "toricJoinDim",
    "toricSecantExpectedDim",
    "toricSecantMatroid",
    "isDeficient",
    "deficientSecants",
    "linearDim",
    "fillingRank",
    "segreAMatrix",
    "veroneseAMatrix",
    "entriesAMatrix",
    "symEntriesAMatrix",
    "matrixEntriesToString",
    "sumPointSet",
    "productPointSet"
    }
protect \ {}
--------------------------------------------------------------------

kk = ZZ/32003

aMatrix = method()
aMatrix(Matrix) := M -> aMatrix(flatten entries M)
aMatrix(RingElement) := m -> aMatrix({m})
aMatrix(List) := L ->
    transpose matrix for m in L list first first (listForm m)
aMatrix(ToricDivisor) := T -> latticePoints T


imageMonomials = method()
imageMonomials(List,Matrix) := (varList,A) -> (
    A = transpose A;
    M := for r in entries A list product(#r, j->(varList#j)^(r#j));
    matrix {M}
    )


homogenizeAMatrix = method()
homogenizeAMatrix(Matrix) := A -> (
    n := numrows A;
    N := numcols A;
    colSums := matrix{toList(n:1)}*A;
    d := max flatten entries colSums;
    A||(matrix{toList(N:d)}-colSums)
    )


toricJoinDim = method()
toricJoinDim(Matrix,Matrix) := (A,B) -> toricJoinDim({A,B})
toricJoinDim(List) := L -> (
    n := L/numrows;
    randPoints := apply(#L, i->randomPoint(kk,n#i));
    J := apply(L, aJac);
    tSpace := matrix apply(#L, i->{sub(J#i,randPoints#i)});
    rank tSpace
    )

--Randomized algorithm for dim of kth secant of variety defined by toric divisor T.
--Returns triple of dim of secant, expected dim, and boolean whether they match.
--toricSecantDim has counterpart tsd that takes a matrix whose columns are the integer lattice points of a polytope, instead of T.
toricSecantDim = method()
toricSecantDim(Matrix,ZZ) := (A,k) -> (
    n := numrows A;
    randPoints := apply(k,i->randomPoint(kk,n));
    J := aJac A;
    tSpace := matrix apply(randPoints, p->{sub(J,p)});
    rank tSpace
    )


toricSecantMatroid = method()
toricSecantMatroid(Matrix,ZZ) := (A,k) -> (
    n := numrows A;
    randPoints := apply(k,i->randomPoint(kk,n));
    J := aJac A;
    tSpace := matrix apply(randPoints, p->{sub(J,p)});
    matroid tSpace
    )

randomPoint = (K,n) -> random(K^1,K^n)

aJac = A -> (
    n := numrows A;
    x := symbol x;
    R := kk[x_0..x_(n-1)];
    jacobian imageMonomials(gens R,A)
    )


toricSecantExpectedDim = method()
toricSecantExpectedDim(Matrix,ZZ) := (A,k) -> (
    D := linearDim A;
    min{D,k*(rank A)};
    )


linearDim = method()
linearDim(Matrix) := A -> (
    cols := apply(numcols A, i->A_i);
    #(unique cols)
    )


fillingRank = method()
fillingRank(Matrix) := A -> (
    D := linearDim A;
    d := 0;
    k := 0;
    while d < D do (
	k = k+1;
	d = toricSecantDim(A,k);
	);
    k
    )
	

--Takes a toric divisor T and returns true if any secant of the variety is deficient.
isDeficient = method()
isDeficient(Matrix,ZZ) := (A,k) -> toricSecantDim(A,k) != toricSecantExpectedDim(A,k)
isDeficient(Matrix) := A -> (
    (n,N) := (numrows A, numcols A);
    not (isDeficient(A,N//(n+1)) and isDeficient(A,(N//(n+1))+1))
    )

--Takes a toric divisor T and returns a list of triples, one for each dificent secant.
--Each triple is the secant number, the dimension of the secant, and the amount it is deficient by.
--For some reason it cuts off at secant 200 (I don't know why I have that bound in there).
--defienctSecants has counterpart ds that takes a matrix whose columns are the integer lattice points of a polytope, instead of T.
deficientSecants = method()
deficientSecants(Matrix) := A -> (
    D := linearDim A;
    d := 0;
    k := 0;
    while d < D list (
	k = k+1;
	d = toricSecantDim(A,k);
	e := toricSecantExpectedDim(A,k);
	if d != e then (k,d,e) else continue
	)
    )

-------------------------------------------------
-- Ideals

--computes the nth secant of ideal I using elimination
--if degree d is specified, then the generators up to degree d will be computed (this is much faster)
secant = method(Options=>{DegreeLimit => {}})
secant(Ideal,ZZ) := opts -> (I,n) -> joinIdeal(toList (n:I), opts)

joinIdeal = method(Options=>{DegreeLimit => {}})
joinIdeal(Ideal,Ideal) := opts -> (I,J) -> joinIdeal({I,J},opts)
joinIdeal(List) := opts -> L -> (
    R := ring first L;
    k := numgens R;
    n := #L;
    T := R;
    for i from 0 to n-1 do T = T**R;
    T = newRing(T, MonomialOrder=>Eliminate(n*k));
    Jlinears := apply(k,j->T_(n*k+j) - sum(n,i->T_(i*k+j)));
    Js := apply(n, i->sub(L#i,(vars T)_(toList(i*k..(i+1)*k-1))));
    J := sum(Js) + ideal Jlinears;
    d := opts.DegreeLimit;
    GB := gb(J, DegreeLimit=>join((n+1):d));
    J = selectInSubring(1,gens GB);
    ideal sub(J,matrix{toList (n*k:0_R)}|(vars R))
    )


-------------------------------------------------
-- Segre products (i.e. matrices and tensors)

--produce the A matrix for a segre product of affine spaces with sizes = (k_1,...,k_n)
segreAMatrix = method()
segreAMatrix(Sequence) := sizes -> (
    d := #sizes;
    basisList := for k in sizes list (
	for j from 0 to k-1 list (
	    l := (j:0)|(1:1)|(k-j-1:0);
	    toList l
	    )
	);
    Alist := toList apply((d:1)..sizes, ind->(join toSequence for i from 0 to d-1 list basisList#i#((ind#i)-1)));
    transpose matrix Alist
    )

entriesAMatrix = method()
entriesAMatrix(Sequence,Sequence) := (S,sizes) -> entriesAMatrix(toList S,sizes)
entriesAMatrix(List,Sequence) := (S,sizes) -> (
    transpose matrix toList apply(S, e->entryToVect(e,sizes))
    )

symEntriesAMatrix = method()
symEntriesAMatrix(Sequence,ZZ,ZZ) := (S,n,d) -> symEntriesAMatrix(toList S,n,d)
symEntriesAMatrix(List,ZZ,ZZ) := (S,n,d) -> (
    A := for e in S list (
	a := new MutableList from (n:0);
	for i in e do a#i = a#i+1;
	toList a
	);
    transpose matrix A
    )

matrixEntriesToString = method()
matrixEntriesToString(ZZ,ZZ,List) := (n,m,S) -> (
    S = sort S;
    i := 0;
    strList := for k from 0 to n-1 list (
    	L := for s in (k,0)..(k,m-1) list if S#?i and s == S#i then (i = i+1; "#") else ".";
	concatenate{L,"\n"}
	);
    concatenate strList
    )

entryToVect = (ent,sizes) -> (
    vect := for i from 0 to #ent-1 list join((ent#i:0),(1:1),(sizes#i-ent#i-1:0));
    toList join(toSequence vect)
    )


veroneseAMatrix = method()
veroneseAMatrix(ZZ,ZZ) := (n,d) -> (
    x := symbol x;
    R := kk[x_0..x_(n-1)];
    aMatrix basis(d,R)
    )
    



-------------------------------------------------
-- Point sets

sumPointSet = method()
sumPointSet(Matrix,Matrix) := (P,Q) -> (
    P = entries transpose P;
    Q = entries transpose Q;
    PQ := for I in (0,0)..(#P-1,#Q-1) list P#(I#0) + Q#(I#1);
    transpose matrix unique PQ
    )

productPointSet = method()
productPointSet(Matrix,Matrix) := (P,Q) -> (
    P = entries transpose P;
    Q = entries transpose Q;
    PQ := flatten for p in P list for q in Q list p|q;
    transpose matrix PQ
    )

randomPointSet = (d,k,B) -> (
    Pdim := 0;
    Pmat := null;
    while Pdim != d do (
	n := 0;
    	P := {};
    	while n < k do (
	    newP := toList apply(k-n, j-> apply(d, i->random(B)));
	    P = unique (P|newP);
	    n = #P;
	    );
	Pmat = transpose matrix sort P;
	Pdim = dim convexHull Pmat;
	);
    Pmat
    )	

randomPolytope = (d,k,B) -> (
    P := null;
    Pdim := 0;
    while Pdim != d do (
    	L := matrix toList apply(d,i->toList apply(k,j->random(B)));
    	P = convexHull L;
	Pdim = dim P;
	);
    P
    )

----------------------------------------------------------
-- Documentation
----------------------------------------------------------
beginDocumentation()

-------------------------------
-- PhylogeneticTrees
-------------------------------
doc///
    Key
	ToricSecants
    Headline
        A package to compute dimensions of secants of toric varieties
    Description
        Text
	    Matrix and tensor rank varieties are examples of secants of affine toric varieties,
	    as are their coordinate projections.  Many questions about low rank matrix and 
	    tensor completion can be rephrased as questions about dimensions of toric secants.
	    The Alexander-Hirschowitz theorem is a result about such varieties, but many
	    more questions remain.  For more general toric varieties, things are wide open.
	    
	    A toric variety embedded in affine space can be described as the image of
	    a monomial map.  Such a map is specified by its "A-matrix", the matrix
	    whose columns are the exponent vectors of the monomials.  This package
	    computes dimensions of secants and joins of toric varieties from the A-matrix,
	    using Terracini's lemma.
	    
	    The variety of rank 1 $n\times m$ matrices is a toric variety. A rank 1 matrix
	    is the outter-product of two parameter vectors, so each entry is a monomial
	    of degree 2 of the parameter variables.  This variety is also a Segre product of 
	    two affine spaces.  The following produces the A-matrix for $3 \times 4$ matrices:
	Example
	    (n,m) = (3,4)
	    A = segreAMatrix(1:oo)
	Text
	    This package does not produce the defining equations of the toric variety.  For that, use the
	    {\tt FourTiTwo} package.  It will compute the dimensions of the secants, which
	    are the varieties of the higher rank matrices:
	Example
	    toricSecantDim(A,1)
	    toricSecantDim(A,2)
	    toricSecantDim(A,3)
	    toricSecantDim(A,4)
	Text
	    For generic matrix completion problems, we want to understand the algebraic dependencies
	    between entries.  This is represented by an algebraic matroid.
	Example
	    M = toricSecantMatroid(A,2)
	    C = circuits M;
	    ents = (0,0)..(n-1,m-1);
	    apply(C, c->matrixEntriesToString(n,m,apply(toList c, e->ents#e)))
	Text
	    We also want to project
	    rank varieties on to subsets of the coordinates.  These are also secants of toric
	    varieties, with A-matrices given by taking a subset of the columns of the A-matrix
	    of the full rank 1 matrix variety.
	    
	    A subset $S \subseteq [n]\times [m]$ of entries
	    can be generically completed to rank {\tt r} if and only if the projection of the variety of
	    rank {\tt r} matrices onto these coordinates is dominant.
	Example
	    S = {(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)};
	    matrixEntriesToString(3,3,S)
	    A = entriesAMatrix(S,(3,3))
	    toricSecantDim(A,1)
	    toricSecantDim(A,2)
	Text
	    The above example shows that the set {\tt S} is not completable to rank 1 because
	    the dimension is 5, which is less than the size of {\tt S}.  It is completable to
	    rank 2.  To find the generic completion rank,
	Example
	    fillingRank A
	Text
	    The variety of $n\times n$ symmetric matrices are represented by the second veronese
	    embedding of {\tt n} dimensional affine space.  The A-matrix of the full rank 1 variety
	    or partial fillings can be produced as follows:
	Example
	    A = veroneseAMatrix(4,2)
	    S = {(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3)};
	    B = symEntriesAMatrix(S,4,2)
	    
///
-------------------------------
-- aMatrix
doc///
    Key
        aMatrix
	(aMatrix,Matrix)
        (aMatrix,RingElement)
        (aMatrix,List)
        (aMatrix,ToricDivisor)
    Headline
        A-matrix of a monomial map
    Usage
	A = aMatrix M
	A = aMatrix m
	A = aMatrix L
	A = aMatrix T
    Inputs
	M:Matrix
	    a matrix of a monomials
	m:RingElement
	    a monomial
	L:List
	    a list of monomials
	T:ToricDivisor
    Outputs
	A:Matrix
	    the A-matrix of the toric variety
    Description
        Text
	    Produces the matrix whose columns are the exponent vectors of the input monomials
        Example
	    R = QQ[x,y,z];
	    M = basis(2,R)
	    aMatrix M
    SeeAlso
        imageMonomials
///
-------------------------------
-- segreAMatrix
doc///
    Key
        segreAMatrix
	(segreAMatrix,Sequence)
    Headline
        A-matrix of a Segre variety
    Usage
	A = segreAMatrix D
    Inputs
	D:Sequence
	    a sequence of positive integer dimensions
    Outputs
	A:Matrix
	    the A-matrix of a Segre embedding of affine spaces
    Description
        Text
	    Let $V_1,\ldots,V_k$ be affine spaces with $d_i$ the dimension of $V_i$. Applying
	    {\tt segreAMatrix} to the sequence {\tt D} = $(d_1,\ldots,d_k)$ produces the 
	    A-matrix for the Segre emdedding of $V_1 \times \cdots \times V_k$ into a space
	    of dimension $d_1 \cdots d_k$.
        Example
	    segreAMatrix(1:(2,2,2))
	Text
	    An equivalent definition of the Segre variety is the set of rank 1 (or "pure") tensors
	    in a tensor space of size $d_1 \times \cdots \times d_k$.  When {\tt D = (n,m)},
	    the Segre variety is the set of rank 1 $n\times m$ matrices.  Its {\tt r}th secant is
	    the variety of matrices of rank at most {\tt r}.
	Example
	    A = segreAMatrix(1:(3,4))
	    toricSecantDim(A,2)
    SeeAlso
        aMatrix
	veroneseAMatrix
///
-------------------------------
-- veroneseAMatrix
doc///
    Key
        veroneseAMatrix
	(veroneseAMatrix,ZZ,ZZ)
    Headline
        A-matrix of a Veronese variety
    Usage
	A = veroneseAMatrix(n,d)
    Inputs
	n:ZZ
	    the affine dimension
	d:ZZ
	    the degree of the embedding
    Outputs
	A:Matrix
	    the A-matrix of the degree {\tt d} veronese embedding of the space
    Description
        Text
	    Let {\tt V} be an affine space with dimension {\tt n}. The degree {\tt d} embedding of
	    {\tt V} is a monomial map given by all monmoials in {\tt n} variables of degree {\tt d}.
	    The A-matrix of this map is given by {\tt veroneseAMatrix(n,d)}.
        Example
	    veroneseAMatrix(3,3)
	Text
	    An equivalent definition of the Veronese variety is the set of rank 1 (or "pure")
	    symmetric order-{\tt d} tensors of size $n \times \cdots \times n$.  When {\tt d = 2},
	    the Veronese variety is the set of rank 1 $n\times n$ symmetric matrices.  Its {\tt r}th secant is
	    the variety of symmetric matrices of rank at most {\tt r}.
	Example
	    A = veroneseAMatrix(4,2)
	    toricSecantDim(A,2)
    SeeAlso
        aMatrix
	segreAMatrix
///
-------------------------------
-- entriesAMatrix
doc///
    Key
        entriesAMatrix
	(entriesAMatrix,List,Sequence)
    Headline
        partial A-matrix of a Segre variety
    Usage
	A = entriesAMatrix(S,D)
    Inputs
        S:List
	    a list of entries
	D:Sequence
	    a sequence of positive integer dimensions
    Outputs
	A:Matrix
	    the partial A-matrix of a Segre embedding with columns corresponding to {\tt S}
    Description
        Text
	    The image of the monomial map associated to {\tt A} is the projection of the Segre
	    embedding of a product of affine spaces with dimensions given by the sequence {\tt D}
	    on to the coordinates indicated by the list {\tt S}.
	    
	    For {\tt D} = $(d_1,\ldots,d_k)$, each element of {\tt S} should be a sequence of
	    integers of length {\tt k} with {\tt i}th entry between 0 and $d_i-1$.
        Example
	    S = {(0,0),(0,1),(1,0)}
	    A = entriesAMatrix(S,(3,2))
    SeeAlso
        symEntriesAMatrix
	segreAMatrix
///
-------------------------------
-- symEntriesAMatrix
doc///
    Key
        symEntriesAMatrix
	(symEntriesAMatrix,List,ZZ,ZZ)
    Headline
        partial A-matrix of a Veronese variety
    Usage
	A = entriesAMatrix(S,n,d)
    Inputs
        S:List
	    a list of entries
	n:ZZ
	    the affine dimension
	d:ZZ
	    the degree of the embedding
    Outputs
	A:Matrix
	    the partial A-matrix of a Veronese variety with columns corresponding to {\tt S}
    Description
        Text
	    The image of the monomial map associated to {\tt A} is the projection of the {\tt d}th
	    Veronese embedding of {\tt d}-dimensional affine space
	    on to the coordinates indicated by the list {\tt S}.
	    
	    Each element of {\tt S} should be a sequence of integers between 0 and {\tt n}-1
	    of length {\tt d}.
        Example
	    S = {(0,0),(0,1),(1,2)}
	    A = symEntriesAMatrix(S,3,2)
    SeeAlso
        entriesAMatrix
	veroneseAMatrix
///
-------------------------------
-- toricSecantDim
doc///
    Key
        toricSecantDim
	(toricSecantDim,Matrix,ZZ)
    Headline
        dimension of a secant of a toric variety
    Usage
	d = toricSecantDim(A,k)
    Inputs
	A:Matrix
	    the A-matrix of a toric variety
	k:ZZ
	    the order of the secant
    Outputs
	d:ZZ
	    the dimension of the {\tt k}th secant of variety defined by matrix {\tt A}
    Description
        Text
	    A randomized algorithm for computing the affine dimension of a secant of a toric variety,
	    using Terracini's Lemma.

	    Setting $k$ to 1 gives the dimension of the toric variety, while 2 is the usual secant, and higher
	    values correspond to higher order secants.

	    The matrix $A$ defines a parameterization of the variety.  $k$ vectors of parameter values
	    are chosen at random from a large finite field.  The dimension of the sum of the tangent spaces
	    at those points is computed.

	    This algorithm is much much faster than computing the secant variety.
        Example
	    A = matrix{{4,3,2,1,0},{0,1,2,3,4}}
	    toricSecantDim(A,1)
            toricSecantDim(A,2)
	    toricSecantDim(A,3)
	    toricSecantDim(A,4)
    SeeAlso
	toricJoinDim
	secant
///
-------------------------------
-- toricJoinDim
doc///
    Key
        toricJoinDim
	(toricJoinDim,Matrix,Matrix)
	(toricJoinDim,List)
    Headline
        dimension of a join of toric varieties
    Usage
	d = toricJoinDim(A,B)
	d = toricJoinDim L
    Inputs
	A:Matrix
	    the A-matrix of a toric variety
	B:Matrix
	    the A-matrix of a toric variety
	L:List
	    a list of A-matrices of toric varieties
    Outputs
	d:ZZ
	    the dimension of the join of the toric varieties defined by the matrices
    Description
        Text
	    A randomized algorithm for computing the affine dimension of a join of toric varieties,
	    using Terracini's Lemma.

	    Each input matrix defines a parameterization of the variety.  For each, a vector of parameter values
	    is chosen at random from a large finite field.  The dimension of the sum of the tangent spaces
	    at those points is computed.

	    This algorithm is much much faster than computing the join variety.
        Example
	    A = matrix{{4,3,2,1,0},{0,1,2,3,4}}
	    B = matrix{{1,1,1,1,1}}
	    toricJoinDim(A,B)
	    toricJoinDim(B,B)
    Caveat
	All input matrices must have the same number of columns.
    SeeAlso
	toricSecantDim
	joinIdeal
///
-------------------------------
-- fillingRank
doc///
    Key
        fillingRank
	(fillingRank,Matrix)
    Headline
        first secant that fills the space
    Usage
	r = fillingRank A
    Inputs
	A:Matrix
	    the A-matrix of a toric variety
    Outputs
	r:ZZ
	    the first secant that fills the space
    Description
        Text
	    For any variety {\tt V}, there is some {\tt r} for which the {\tt r}th secant of
	    {\tt V} is the entire linear span of {\tt V}.  This function finds the minimum
	    such {\tt r} for the affine toric variety with A-matrix {\tt A}.
        Example
	    A = matrix{{4,3,2,1,0},{0,1,2,3,4}}
	    fillingRank A
    SeeAlso
	toricSecantDim
///
-------------------------------
-- toricSecantMatroid
doc///
    Key
        toricSecantMatroid
	(toricSecantMatroid,Matrix,ZZ)
    Headline
        algebraic coordinate matroid of a toric secant
    Usage
	d = toricSecantMatroid(A,k)
    Inputs
	A:Matrix
	    the A-matrix of a toric variety
	k:ZZ
	    the order of the secant
    Outputs
	M:Matroid
	    the algebraic coordinate matroid of the {\tt k}th secant of variety defined by matrix {\tt A}
    Description
        Text
	    The algebraic coordinate matroid of a variety in affine space is the matroid with ground set
	    the coordinate variables, and dependence relations defined by the algebraic relations in the 
	    coordinate ring of the variety.  Equivalently, the rank function maps a set of coordinates 
	    to the dimension of the projection of the variety on to those coordinates.

	    This is a randomized algorithm for computing the algebraic matroid using Terracini's Lemma.
        Example
	    A = matrix{{4,3,2,1,0},{0,1,2,3,4}}
	    M = toricSecantMatroid(A,2)
	    bases M
	    circuits M
    SeeAlso
	toricSecantDim
///
-------------------------------
-- linearDim
doc///
    Key
        linearDim
	(linearDim,Matrix)
    Headline
        dimension of the linear span of a toric variety
    Usage
	d = linearDim A
    Inputs
	A:Matrix
	    the A-matrix of a toric variety
    Outputs
	d:ZZ
	    the dimension of the linear span of the variety
    Description
        Text
	    Typically the linear span of a toric variety is the full ambient space, which is
	    the number of columns of {\tt A}.  The only
	    exception is when a column of {\tt A} is repeated.  In this case, the variables
	    corresponding to this column will always be equal.
        Example
	    A = matrix{{2,1,1,0},{0,1,1,2}}
	    linearDim A
///
-------------------------------
-- Secants and Joins
-------------------------------
-- secant
doc///
    Key
	secant
	(secant,Ideal,ZZ)
	[secant,DegreeLimit]
    Headline
	computes the secant of an ideal
    Usage
	J = secant(I,n)
    Inputs
	I:Ideal
	    an ideal of a ring R
	k:ZZ
	    the order of the secant
    Outputs
	J:Ideal
	    the {\tt k}th secant of {\tt I}
    Description
	Text
	    Computes the $k$th secant of $I$ by constructing the abstract secant and then projecting with elimination.

	    Setting $k$ to 1 gives the dimension of the ideal, while 2 is the usual secant, and higher
	    values correspond to higher order secants.

	    Setting the optional argument @TO DegreeLimit@ to $\{d\}$ will produce only the generators
	    of the secant ideal up to degree $d$.

	    This method is general and will work for arbitrary polynomial ideals, not just phylogenetic ideals.
	Example
	    R = QQ[a..d]
	    I = ideal {a^2-b,a^3-c,a^4-d}
	    secant(I,2)
    SeeAlso
        joinIdeal
///
-------------------------------
-- joinIdeal
doc///
    Key
	joinIdeal
	(joinIdeal,Ideal,Ideal)
	(joinIdeal,List)
	[joinIdeal,DegreeLimit]
    Headline
	computes the join of several ideals
    Usage
	K = joinIdeal(I,J)
	K = joinIdeal L
    Inputs
	I:Ideal
	    an ideal of a ring R
	J:Ideal
	    another ideal of R
	L:List
	    a list of ideals in the same ring
    Outputs
	K:Ideal
	    the join of the input ideals
    Description
	Text
	    Computes the join by constructing the abstract join and then projecting with elimination.

	    Setting the optional argument @TO DegreeLimit@ to $\{d\}$ will produce only the generators
	    of the secant ideal up to degree $d$.

	    This method is general and will work for arbitrary polynomial ideals, not just phylogenetic ideals.
	Example
	    R = QQ[a,b,c,d]
	    I = ideal {a-d,b^2-c*d}
	    J = ideal {a,b,c}
	    joinIdeal(I,J)
    SeeAlso
        secant
///