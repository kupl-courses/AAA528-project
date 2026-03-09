predicate sorted(a: array<int>, l: int, u: int)
{
	forall j, k :: 0 <= l <= j <= k <= u < a.Length ==> a[j] <= a[k]
}

predicate partitioned(a: array<int>, l1: int, u1: int, l2: int, u2: int)
{
	forall x, y :: 0 <= l1 <= x <= u1 < l2 <= y <= u2 < a.Length ==> a[x] <= a[y]
}

method BinarySearchWhile_Incorrect(a: array<int>, value: int) returns (index : int)
	requires 0 <= a.Length && sorted(a, 0, a.Length - 1)
	ensures (0 <= index ==> index < a.Length && a[index] == value) 
	ensures (index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value)
{
  var low : int := 0; 
  var high : int := a.Length; 
  var mid : int;

  while (low < high)
    invariant sorted(a, 0, a.Length - 1) 
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 < i < low ==> a[i] != value   
    invariant forall i :: high <= i < a.Length ==> a[i] != value
  {
    mid := (low + high) / 2;
    if (a[mid] < value) { low := mid + 1; }
    else if (value < a[mid]) { high := mid; }
    else { return mid; }
  }
  return -1;
}

method BinarySearchWhile_Correct(a: array<int>, value: int) returns (index : int)
	requires 0 <= a.Length && sorted(a, 0, a.Length - 1)
	ensures (0 <= index ==> index < a.Length && a[index] == value) 
	ensures (index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value)
{
  var low : int := 0; 
  var high : int := a.Length; 
  var mid : int;

  while (low < high)
    invariant sorted(a, 0, a.Length - 1) 
    invariant 0 <= low <= high <= a.Length
    invariant 0 < low ==> a[0] != value 
    invariant forall i :: 0 < i < low ==> a[i] != value   
    invariant forall i :: high <= i < a.Length ==> a[i] != value
  {
    mid := (low + high) / 2;
    if (a[mid] < value) { low := mid + 1; }
    else if (value < a[mid]) { high := mid; }
    else { return mid; }
  }
  return -1;
}

method BubbleSort_Incorrect (a0: array<int>) returns (a: array<int>)
  requires a0.Length >= 0 && a0.Length < 4
	ensures sorted(a, 0, a.Length - 1) 
{
    var i : int;
    var j : int;  

    a := a0;   
    i := a.Length - 1;

	while (i > 0)
		invariant -1 <= i < a.Length && a.Length < 4
		invariant partitioned (a, 0, i, i+1, a.Length - 1)
		invariant sorted (a, i, a.Length - 1)
	{
		j := 0;
		while (j < i) 
			invariant 1 <= i < a.Length && 0 <= j <= i && a.Length < 4
			invariant partitioned (a, 0, i, i + 1, a.Length - 1)
			invariant partitioned (a, 0, j - 1, j, j)
			invariant sorted (a, i, a.Length - 1)
		{
			if (a[j] > a[j+1]) {
        a[j], a[j+1] := a[j+1], a[j];
			}
			j := j + 1;
		}
		i := i - 1;
	}
}

method BubbleSort_Correct (a0: array<int>) returns (a: array<int>)
  requires a0.Length >= 0 && a0.Length < 4
	ensures sorted(a, 0, a.Length - 1) 
{
    var i : int;
    var j : int;  

    a := a0;   
    i := a.Length - 1;

	while (i > 0)
		invariant -1 <= i < a.Length && a.Length < 4
		invariant i < 0 ==> a.Length == 0 
		invariant partitioned (a, 0, i, i+1, a.Length - 1)
		invariant sorted (a, i, a.Length - 1)
	{
		j := 0;
		while (j < i) 
			invariant 1 <= i < a.Length && 0 <= j <= i && a.Length < 4
			invariant partitioned (a, 0, i, i + 1, a.Length - 1)
			invariant partitioned (a, 0, j - 1, j, j)
			invariant sorted (a, i, a.Length - 1)
		{
			if (a[j] > a[j+1]) {
        a[j], a[j+1] := a[j+1], a[j];
			}
			j := j + 1;
		}
		i := i - 1;
	}
}

method FindMax_Incorrect (a: array<int>) returns (r: int)
	requires 0 < a.Length 
	ensures forall k :: 0 <= k < a.Length ==> a[k] <= r
  ensures exists k :: 0 <= k < a.Length && a[k] == r
{
	var i : int := 0;
	r := a[0];
	while (i < a.Length)
		invariant a.Length > 0 
		invariant 0 <= i <= a.Length
		invariant forall k :: 0 <= k < i ==> r >= a[k]
		invariant exists k :: 0 <= k < i && a[k] == r
	{
		if(a[i] > r) { r := a[i]; }
		i := i + 1;
	}
}


method FindMax_Correct (a: array<int>) returns (r: int)
	requires 0 < a.Length 
	ensures forall k :: 0 <= k < a.Length ==> a[k] <= r
  ensures exists k :: 0 <= k < a.Length && a[k] == r
{
	var i : int := 0;
	r := a[0];
	while (i < a.Length)
		invariant a.Length > 0 
		invariant 0 <= i <= a.Length
		invariant forall k :: 0 <= k < i ==> r >= a[k]
		invariant (a[0] == r || exists k :: 0 <= k < i && a[k] == r)
	{
		if(a[i] > r) { r := a[i]; }
		i := i + 1;
	}
}

function Dist(x: int, y: int): int {
    if (x < y) then y - x else x - y
}

method CanyonSearch_Incorrect(a: array<int>, b: array<int>) returns (d: int)
    requires a.Length > 0 && b.Length > 0 
    requires sorted(a, 0, a.Length - 1) && sorted(b, 0, b.Length - 1)
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i], b[j])
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i], b[j])
{
    var m : int := 0; 
		var n : int := 0; 
    d := Dist(a[0], b[0]);
    
    while (m < a.Length andalso n < b.Length) 
				invariant sorted(a, 0, a.Length - 1) && sorted(b, 0, b.Length - 1)
        invariant 0 <= m <= a.Length && 0 <= n <= b.Length
        invariant exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i], b[j])
        invariant forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i], b[j]) // || (m <= i && n <= j)
    {
        d :=  if (Dist(b[n], a[m]) < d) then Dist(b[n], a[m]) else d;
        if (a[m] <= b[n]) {
					m := m + 1;
				} else {
					n := n + 1;
				}
    }
}

method CanyonSearch_Correct(a: array<int>, b: array<int>) returns (d: int)
    requires a.Length > 0 && b.Length > 0 
    requires sorted(a, 0, a.Length - 1) && sorted(b, 0, b.Length - 1)
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i], b[j])
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i], b[j])
{
    var m : int := 0; 
		var n : int := 0; 
    d := Dist(a[0], b[0]);
    
    while (m < a.Length andalso n < b.Length) 
				invariant sorted(a, 0, a.Length - 1) && sorted(b, 0, b.Length - 1)
        invariant 0 <= m <= a.Length && 0 <= n <= b.Length
        invariant exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i], b[j])
        invariant forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i], b[j]) || (m <= i && n <= j)
    {
        d :=  if (Dist(b[n], a[m]) < d) then Dist(b[n], a[m]) else d;
        if (a[m] <= b[n]) {
					m := m + 1;
				} else {
					n := n + 1;
				}
    }
}

predicate IsEven(n: int) 
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FirstEven_Incorrect(a: array<int>) returns (n: int)
    requires a.Length >= 2 && a.Length <= 6
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    ensures exists i :: 0 <= i < a.Length && IsEven(a[i]) && n == a[i] && (forall k :: 0 <= k < i ==> IsOdd(a[k]))
{
    var firstEven : int := -1;
    var i : int := 0;

    while (i < a.Length)
        invariant 0 <= i <= a.Length
        invariant 0 <= firstEven < i ==> IsEven(a[firstEven]) //wrong
        //invariant (0 <= firstEven < i) || firstEven == -1 //to be added
        invariant firstEven == -1 ==> (forall k :: 0 <= k < i ==> !IsEven(a[k]))
        invariant firstEven != -1 ==> (forall k :: 0 <= k < firstEven ==> IsOdd(a[k]))
        /***************** Dafny doesn't need the below invariants *****************/
        invariant a.Length >= 2 && a.Length <= 6
        invariant exists i :: 0 <= i < a.Length && IsEven(a[i])
        invariant firstEven != -1 && IsEven(a[i]) ==> firstEven == i 
        invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
    {
        if (firstEven == -1 andalso IsEven(a[i]))
        {
            firstEven := i;
            break;
        }
        i := i + 1;
    }
    n := a[firstEven];
}


method FirstEven_Correct(a: array<int>) returns (n: int)
    requires a.Length >= 2 && a.Length <= 6
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    ensures exists i :: 0 <= i < a.Length && IsEven(a[i]) && n == a[i] && (forall k :: 0 <= k < i ==> IsOdd(a[k]))
{
    var firstEven : int := -1;
    var i : int := 0;

    while (i < a.Length)
        invariant 0 <= i <= a.Length
        invariant (firstEven == -1 || (0 <= firstEven && firstEven < i && IsEven(a[firstEven]))) //correct invariant
        invariant firstEven == -1 ==> (forall k :: 0 <= k < i ==> !IsEven(a[k]))
        invariant firstEven != -1 ==> (forall k :: 0 <= k < firstEven ==> IsOdd(a[k]))
        /***************** Dafny doesn't need the below invariants *****************/
        invariant a.Length >= 2 && a.Length <= 6
        invariant exists i :: 0 <= i < a.Length && IsEven(a[i])
        invariant firstEven != -1 && IsEven(a[i]) ==> firstEven == i 
        invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
    {
        if (firstEven == -1 andalso IsEven(a[i]))
        {
            firstEven := i;
            break;
        }
        i := i + 1;
    }
    n := a[firstEven];
}

method FirstEvenOddDifference_Incorrect (a: array<int>) returns (diff: int)
    requires a.Length >= 2 && a.Length <= 6
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
{
    var firstEven : int := -1;
    var firstOdd : int := -1;
    var i : int := 0;

    while (i < a.Length)
        invariant 0 <= i <= a.Length
        invariant 0 <= firstEven < i ==> IsEven(a[firstEven]) //wrong invariant 
        //invariant (0 <= firstEven && firstEven < i) || firstEven == -1 // to be added
        invariant (firstOdd == -1 || (0 <= firstOdd && firstOdd < i && IsOdd(a[firstOdd]))) // 위와 마찬가지
        //invariant 0 <= firstOdd && firstOdd < i ==> IsOdd(a[firstOdd]) 
        invariant firstEven == -1 ==> (forall k :: 0 <= k < i ==> !IsEven(a[k]))
        invariant firstOdd == -1 ==> (forall k :: 0 <= k < i ==> !IsOdd(a[k]))
        invariant firstEven != -1 ==> (forall k :: 0 <= k < firstEven ==> IsOdd(a[k]))
        invariant firstOdd != -1 ==> (forall k :: 0 <= k < firstOdd ==> IsEven(a[k]))
        /***************** Dafny doesn't need the below invariants *****************/
        invariant a.Length >= 2 && a.Length <= 6
        invariant exists i :: 0 <= i < a.Length && IsEven(a[i]) 
        invariant exists i :: 0 <= i < a.Length && IsOdd(a[i]) 
        invariant firstEven != -1 && firstOdd != -1 ==> ((firstEven < firstOdd ==> i == firstOdd) && (firstOdd < firstEven ==> i == firstEven)) 
    {
        if (firstEven == -1 andalso IsEven(a[i]))
        {
            firstEven := i;
        }
        if (firstOdd == -1 andalso IsOdd(a[i]))
        {
            firstOdd := i;
        }
        if (firstEven != -1 andalso firstOdd != -1)
        {
            break;
        }
        i := i + 1;
    }
    diff := a[firstEven] - a[firstOdd];
}


method FirstEvenOddDifference_Correct (a: array<int>) returns (diff: int)
    requires a.Length >= 2 && a.Length <= 6
    requires exists i :: 0 <= i && i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i && i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i && i < a.Length && 0 <= j && j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
{
    var firstEven : int := -1;
    var firstOdd : int := -1;
    var i : int := 0;

    while (i < a.Length)
        invariant 0 <= i && i <= a.Length
        invariant (firstEven == -1 || (0 <= firstEven && firstEven < i && IsEven(a[firstEven]))) 
        invariant (firstOdd == -1 || (0 <= firstOdd && firstOdd < i && IsOdd(a[firstOdd]))) 
        invariant firstEven == -1 ==> (forall k :: 0 <= k && k < i ==> !IsEven(a[k]))
        invariant firstOdd == -1 ==> (forall k :: 0 <= k && k < i ==> !IsOdd(a[k]))
        invariant firstEven != -1 ==> (forall k :: 0 <= k && k < firstEven ==> IsOdd(a[k]))
        invariant firstOdd != -1 ==> (forall k :: 0 <= k && k < firstOdd ==> IsEven(a[k]))
        /***************** Dafny doesn't need the below invariants *****************/
        invariant a.Length >= 2 && a.Length <= 6
        invariant exists i :: 0 <= i < a.Length && IsEven(a[i]) 
        invariant exists i :: 0 <= i < a.Length && IsOdd(a[i]) 
        invariant firstEven != -1 && firstOdd != -1 ==> ((firstEven < firstOdd ==> i == firstOdd) && (firstOdd < firstEven ==> i == firstEven)) 
    {
        if (firstEven == -1 andalso IsEven(a[i]))
        {
            firstEven := i;
        }
        if (firstOdd == -1 andalso IsOdd(a[i]))
        {
            firstOdd := i;
        }
        if (firstEven != -1 andalso firstOdd != -1)
        {
            break;
        }
        i := i + 1;
    }
    diff := a[firstEven] - a[firstOdd];
}


predicate beq(a: array<int>, b: array<int>, k1: int, k2: int)
{
  forall i :: k1 <= i <= k2 ==> a[i] == b[i]
}

function random (l: int, u: int) : int
{
	l 
}

method InsertionSort_Incorrect1(a0:array<int>) returns (a:array<int>)
  requires 5 >= a0.Length >= 2 
  ensures sorted(a, 0, a.Length-1)
{
  var x : int := 1;
  var d : int;

  a := a0;

  while (x < a.Length)
    invariant 1 <= x <= a.Length
    invariant sorted(a, 0, x-1)

    //dafny may not need these
    invariant 5 >= a0.Length >= 2
  {
    d := x;
    while (d >= 1 andalso a[d-1] > a[d])
      invariant 0 <= d <= x
      invariant forall i,j :: 0 <= i < j < d ==> a[i] <= a[j] //wrong
      //invariant forall i,j ::( 0 <= i < j <= x && j != d) ==> a[i] <= a[j]  //correct

      //dafny may not need these
      invariant 5 >= a0.Length >= 2
      invariant 1 <= x < a.Length // took some time to figure out
    {
      a[d-1], a[d] := a[d], a[d-1];
      d := d-1;
    }
    x := x + 1;
  }
}

method InsertionSort_Incorect2(a0:array<int>) returns (a:array<int>)
  //modifies a
  requires 5 >= a0.Length >= 2 
  ensures sorted(a, 0, a.Length-1)
{
  var x : int := 1;
  var d : int;

  a := a0;

  while (x < a.Length)
    invariant 1 <= x <= a.Length
    invariant sorted(a, 0, x-1)

    //dafny may not need these
    invariant 5 >= a0.Length >= 2
  {
    d := x;
    while (d >= 1 andalso a[d-1] > a[d])
      invariant 0 <= d <= x
      invariant forall i,j :: 0 <= i < j <= x /* && j != d */ ==> a[i] <= a[j]

      //dafny may not need these
      invariant 5 >= a0.Length >= 2
      invariant 1 <= x < a.Length // took some time to figure out
    {
      a[d-1], a[d] := a[d], a[d-1];
      d := d-1;
    }
    x := x + 1;
  }
}

method InsertionSort_Correct(a0:array<int>) returns (a:array<int>)
  requires 5 >= a0.Length >= 2 
  ensures sorted(a, 0, a.Length-1)
{
  var x : int := 1;
  var d : int;

  a := a0;

  while (x < a.Length)
    invariant 1 <= x <= a.Length
    invariant sorted(a, 0, x-1)

    //dafny may not need these
    invariant 5 >= a0.Length >= 2
  {
    d := x;
    while (d >= 1 andalso a[d-1] > a[d])
      invariant 0 <= d <= x
      // invariant forall i,j :: 0 <= i < j < d ==> a[i] <= a[j] //wrong
      invariant forall i,j ::( 0 <= i < j <= x && j != d) ==> a[i] <= a[j]  //correct

      //dafny may not need these
      invariant 5 >= a0.Length >= 2
      invariant 1 <= x < a.Length // took some time to figure out
    {
      a[d-1], a[d] := a[d], a[d-1];
      d := d-1;
    }
    x := x + 1;
  }
}

method IsPalindrome_Incorrect(x: array<int>) returns (result: bool)
  requires x.Length >= 0
  ensures result <==> (forall i :: 0 <= i < x.Length  ==> x[i] == x[x.Length - i - 1])
{
  var i :int := 0;
  var j :int := x.Length - 1;

  if (x.Length==0) {
    return true;
  }
  
  result := true;
  while (i < j)
    invariant 0 <= i <= j+1 && 0 <= j < x.Length 
    //invariant i + j == x.Length -1 //when omitted, the third invariant & postconditon are not proved
    invariant forall k :: 0 <= k < i ==> x[k] == x[x.Length - k - 1]

    // dafny doesn't need these
    invariant result == false ==> (exists k :: 0 <= k < x.Length && x[k] != x[x.Length - k - 1])
  {
    if (x[i] != x[j]) {
      result := false;
      return result;
    }
    i := i + 1;
    j := j - 1;
  }
}

method IsPalindrome_Correct(x: array<int>) returns (result: bool)
  requires x.Length >= 0
  ensures result <==> (forall i :: 0 <= i < x.Length  ==> x[i] == x[x.Length - i - 1])
{
  var i :int := 0;
  var j :int := x.Length - 1;

  if (x.Length==0) {
    return true;
  }
  
  result := true;
  while (i < j)
    invariant 0 <= i <= j+1 && 0 <= j < x.Length 
    invariant i + j == x.Length -1 //when omitted, the third invariant & postconditon are not proved
    invariant forall k :: 0 <= k < i ==> x[k] == x[x.Length - k - 1]

    // dafny doesn't need these
    invariant result == false ==> (exists k :: 0 <= k < x.Length && x[k] != x[x.Length - k - 1])
  {
    if (x[i] != x[j]) {
      result := false;
      return result;
    }
    i := i + 1;
    j := j - 1;
  }
}


method LucidNumbers_Incorrect(n: int) returns (lucid: array<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < lucid.Length ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < lucid.Length ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < lucid.Length ==> lucid[i] < lucid[j]
{
    // Allocate array with the maximum size needed for multiples of 3
    var maxSize : int := n / 3 + 1;
    var index : int := 0;
    var i : int := 0;
    var resized : array<int>;
    var j : int;
    lucid := new [maxSize];

    while (i <= n)
        invariant 0 <= i <= n + 1
        invariant 0 <= index <= maxSize
        invariant forall j1 :: 0 <= j1 < index ==> lucid[j1] % 3 == 0
        invariant forall j2 :: 0 <= j2 < index ==> lucid[j2] <= i /* -1 */ 
        invariant forall j3, k :: 0 <= j3 < k < index ==> lucid[j3] < lucid[k]

        //dafny doesn't need the below invariants
        invariant lucid.Length == maxSize
    {
        if (i % 3 == 0) {
            if (index < maxSize) {  // Ensure index does not exceed the array bounds
                lucid[index] := i;
                index := index + 1;
            }
        }
        i := i + 1;
    }

    // Resize the array to fit the exact number of elements
    
    resized := new [index];
    j := 0;
    while (j < index)
        invariant 0 <= j <= index 
        invariant forall k :: 0 <= k < j ==> resized[k] == lucid[k]
        invariant forall i :: 0 <= i < index ==> lucid[i] % 3 == 0
        invariant forall i :: 0 <= i < index ==> lucid[i] <= n
        invariant forall i, j4 :: 0 <= i < j4 < index ==> lucid[i] < lucid[j4] 
        
        //dafny doesn't need the below invariants
        invariant lucid.Length == maxSize
        invariant resized.Length == index
    {
        resized[j] := lucid[j];
        j := j + 1;
    }
    lucid := resized;
    
}


method LucidNumbers_Correct(n: int) returns (lucid: array<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < lucid.Length ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < lucid.Length ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < lucid.Length ==> lucid[i] < lucid[j]
{
    // Allocate array with the maximum size needed for multiples of 3
    var maxSize : int := n / 3 + 1;
    var index : int := 0;
    var i : int := 0;
    var resized : array<int>;
    var j : int;
    lucid := new [maxSize];

    while (i <= n)
        invariant 0 <= i <= n + 1
        invariant 0 <= index <= maxSize
        invariant forall j1 :: 0 <= j1 < index ==> lucid[j1] % 3 == 0
        invariant forall j2 :: 0 <= j2 < index ==> lucid[j2] <= i - 1 
        invariant forall j3, k :: 0 <= j3 < k < index ==> lucid[j3] < lucid[k]

        //dafny doesn't need the below invariants
        invariant lucid.Length == maxSize
    {
        if (i % 3 == 0) {
            if (index < maxSize) {  // Ensure index does not exceed the array bounds
                lucid[index] := i;
                index := index + 1;
            }
        }
        i := i + 1;
    }

    // Resize the array to fit the exact number of elements
    
    resized := new [index];
    j := 0;
    while (j < index)
        invariant 0 <= j <= index 
        invariant forall k :: 0 <= k < j ==> resized[k] == lucid[k]
        invariant forall i :: 0 <= i < index ==> lucid[i] % 3 == 0
        invariant forall i :: 0 <= i < index ==> lucid[i] <= n
        invariant forall i, j4 :: 0 <= i < j4 < index ==> lucid[i] < lucid[j4] 
        
        //dafny doesn't need the below invariants
        invariant lucid.Length == maxSize
        invariant resized.Length == index
    {
        resized[j] := lucid[j];
        j := j + 1;
    }
    lucid := resized;
    
}



method Partition_Incorrect(a0: array<int>, l: int, u: int) returns (pivot: int, a: array<int>)
  requires 0 <= l <= u < a0.Length 
  requires partitioned(a0, 0, l - 1, l, u)
  requires partitioned(a0, l, u, u + 1, a0.Length - 1)
  ensures a.Length == a0.Length 
  ensures beq(a, a0, 0, l - 1)
  ensures beq(a, a0, u + 1, a0.Length - 1)
  ensures l <= pivot <= u 
  ensures partitioned(a, l, pivot - 1, pivot, pivot)
  ensures partitioned(a, pivot, pivot, pivot + 1, u)
{
  var pi : int := random(l, u); 
  var pv : int;
  var i : int := l - 1; 
  var j : int := l; 

  a := a0;
  pv := a[pi]; 
  a[pi] := a[u];
  a[u] := pv; 

  while (j < u) 
    // invariant a[u] == pv 
    invariant a.Length == a0.Length 
    invariant beq(a, a0, 0, l - 1)
    invariant beq(a, a0, u + 1, a0.Length - 1)
    invariant l - 1 <= i < j && j <= u 
    invariant forall k :: l <= k <= i ==> a[k] <= pv
    invariant forall k :: i + 1 <= k < j ==> a[k] > pv
  {
    if (a[j] <= pv) {
      i := i + 1;
      a[i], a[j] := a[j], a[i];
    }
    j := j + 1;
  }

  a[i+1], a[u] := a[u], a[i+1];
  return i+1, a; 
}

method Partition_Correct(a0: array<int>, l: int, u: int) returns (pivot: int, a: array<int>)
  requires 0 <= l <= u < a0.Length 
  requires partitioned(a0, 0, l - 1, l, u)
  requires partitioned(a0, l, u, u + 1, a0.Length - 1)
  ensures a.Length == a0.Length 
  ensures beq(a, a0, 0, l - 1)
  ensures beq(a, a0, u + 1, a0.Length - 1)
  ensures l <= pivot <= u 
  ensures partitioned(a, l, pivot - 1, pivot, pivot)
  ensures partitioned(a, pivot, pivot, pivot + 1, u)
{
  var pi : int := random(l, u); 
  var pv : int;
  var i : int := l - 1; 
  var j : int := l; 

  a := a0;
  pv := a[pi]; 
  a[pi] := a[u];
  a[u] := pv; 

  while (j < u) 
    invariant a[u] == pv 
    invariant a.Length == a0.Length 
    invariant beq(a, a0, 0, l - 1)
    invariant beq(a, a0, u + 1, a0.Length - 1)
    invariant l - 1 <= i < j && j <= u 
    invariant forall k :: l <= k <= i ==> a[k] <= pv
    invariant forall k :: i + 1 <= k < j ==> a[k] > pv
  {
    if (a[j] <= pv) {
      i := i + 1;
      a[i], a[j] := a[j], a[i];
    }
    j := j + 1;
  }

  a[i+1], a[u] := a[u], a[i+1];
  return i+1, a; 
}


method ReverseUptoK_Incorrect (s_in: array<int>, k: int) returns (s : array<int>)
    requires 2 <= k <= s_in.Length
    ensures forall i :: 0 <= i < k ==> s[i] == s_in[k - 1 - i]
    ensures forall i :: k <= i < s.Length ==> s[i] == s_in[i]
{
	  var l : int := k - 1; 
	  var i : int := 0; 
    var tmp : int; 
    s := s_in; 

	  while (i < l - i)
		    invariant 0 <= i <= (l + 1)/2
		    invariant forall p :: (0 <= p < i) /*|| (l - i < p && p <= l)*/ ==> s[p] == s_in[l-p]
        //to be added: invariant forall p :: (l - i < p && p <= l) ==> s[p] == s_in[l-p]
		    invariant forall p :: i <= p <= l - i ==> s[p] == s_in[p]
        invariant forall p :: k <= p < s.Length ==> s[p] == s_in[p]
        /********** Dafny doesn't need the invariants below **********/
        invariant 2 <= k <= s.Length 
        invariant l == k - 1 
	  {
        tmp := s[i]; 
        s[i] := s[l - i]; 
        s[l - i] := tmp; 
		    i := i + 1;
	  }

}

method ReverseUptoK_Correct (s_in: array<int>, k: int) returns (s : array<int>)
    requires 2 <= k <= s_in.Length
    ensures forall i :: 0 <= i < k ==> s[i] == s_in[k - 1 - i]
    ensures forall i :: k <= i < s.Length ==> s[i] == s_in[i]
{
	  var l : int := k - 1; 
	  var i : int := 0; 
    var tmp : int; 
    s := s_in; 

	  while (i < l - i)
		    invariant 0 <= i <= (l + 1)/2
		    invariant forall p :: (0 <= p < i) || (l - i < p <= l) ==> s[p] == s_in[l-p]
		    invariant forall p :: i <= p <= l - i ==> s[p] == s_in[p]
        invariant forall p :: k <= p < s.Length ==> s[p] == s_in[p]
        /********** Dafny doesn't need the invariants below **********/
        invariant 2 <= k <= s.Length 
        invariant l == k - 1 
	  {
        tmp := s[i]; 
        s[i] := s[l - i]; 
        s[l - i] := tmp; 
		    i := i + 1;
	  }

}


method SelectionSort1_Incorrect (a0: array<int>) returns (a: array<int>)
	  requires a0.Length >= 0
	  ensures sorted(a, 0, a.Length - 1)
{
	  var i : int := 0;
    var m : int;
    var j : int;
    a := a0;

	  while (i < a.Length)
		    invariant 0 <= i <= a.Length
        invariant partitioned(a, 0, i-1, i, a.Length-1)
		    invariant sorted(a, 0,i-1)
	  {
		    m := i;
        j := i;

        while(j < a.Length)
	          invariant 0 <= i <= a.Length
            invariant partitioned(a, 0, i-1, i, a.Length-1)
		        invariant sorted(a, 0,i-1)
		        invariant i <= j <= a.Length
		        invariant i <= m < a.Length
		        invariant forall k :: i < k < j ==> a[k] >= a[m] //wrong invariant
            //invariant a[i] >= a[m] //to be added
	      {
	      	  if(a[j] < a[m]) { m := j; }
	      	  j := j + 1;
	      }

        a[m], a[i] := a[i], a[m]; 
		    i := i + 1;
	  }
}

method SelectionSort1_Correct (a0: array<int>) returns (a: array<int>)
	  requires a0.Length >= 0
	  ensures sorted(a, 0, a.Length - 1)
{
	  var i : int := 0;
    var m : int;
    var j : int;
    a := a0;

	  while (i < a.Length)
		    invariant 0 <= i <= a.Length
        invariant partitioned(a, 0, i-1, i, a.Length-1)
		    invariant sorted(a, 0,i-1)
	  {
		    m := i;
        j := i;

        while(j < a.Length)
	          invariant 0 <= i <= a.Length
            invariant partitioned(a, 0, i-1, i, a.Length-1)
		        invariant sorted(a, 0,i-1)
		        invariant i <= j <= a.Length
		        invariant i <= m < a.Length
            invariant forall k :: i <= k < j ==> a[k] >= a[m] 
	      {
	      	  if(a[j] < a[m]) { m := j; }
	      	  j := j + 1;
	      }

        a[m], a[i] := a[i], a[m]; 
		    i := i + 1;
	  }
}


method SumOfSquaresOfFirstNOddNumbers_Incorrect (n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    var i : int := 1;
    var k : int := 0;
    sum := 0;

    while (k < n)
        invariant 0 <= k <= n
        invariant sum == k * (2 * k - 1) * (2 * k + 1) / 3
        //invariant i == 2 * k + 1
    {
        sum := sum + i * i;
        i := i + 2;
        k := k + 1;
    }
}

method SumOfSquaresOfFirstNOddNumbers_Correct (n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    var i : int := 1;
    var k : int := 0;
    sum := 0;

    while (k < n)
        invariant 0 <= k <= n
        invariant sum == k * (2 * k - 1) * (2 * k + 1) / 3
        invariant i == 2 * k + 1 
    {
        sum := sum + i * i;
        i := i + 2;
        k := k + 1;
    }
}


