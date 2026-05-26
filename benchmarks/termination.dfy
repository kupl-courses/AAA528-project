method CountUp_Correct(n: int) returns (r: int)
    requires 0 <= n
    ensures r == n
{
    var i : int := 0;
    r := 0;
    while (i < n)
        invariant 0 <= i <= n
        invariant r == i
        decreases n - i
    {
        i := i + 1;
        r := r + 1;
    }
}

method CountUp_Incorrect(n: int) returns (r: int)
    requires 0 <= n
    ensures r == n
{
    var i : int := 0;
    r := 0;
    while (i < n)
        invariant 0 <= i <= n
        invariant r == i
        decreases i
    {
        i := i + 1;
        r := r + 1;
    }
}

method CountDown_Correct(n: int) returns (r: int)
    requires 0 <= n
    ensures r == 0
{
    var i : int := n;
    r := n;
    while (0 < i)
        invariant 0 <= i <= n
        invariant r == i
        decreases i
    {
        i := i - 1;
        r := r - 1;
    }
}

method CountDown_Incorrect(n: int) returns (r: int)
    requires 0 <= n
    ensures r == 0
{
    var i : int := n;
    r := n;
    while (0 < i)
        invariant 0 <= i <= n
        invariant r == i
        decreases n - i
    {
        i := i - 1;
        r := r - 1;
    }
}

method SumOfSquaresOfFirstNOddNumbers_Correct(n: int) returns (sum: int)
    requires 0 <= n
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    var i : int := 1;
    var k : int := 0;
    sum := 0;

    while (k < n)
        invariant 0 <= k <= n
        invariant sum == k * (2 * k - 1) * (2 * k + 1) / 3
        invariant i == 2 * k + 1
        decreases n - k
    {
        sum := sum + i * i;
        i := i + 2;
        k := k + 1;
    }
}

method SumOfSquaresOfFirstNOddNumbers_Incorrect(n: int) returns (sum: int)
    requires 0 <= n
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    var i : int := 1;
    var k : int := 0;
    sum := 0;

    while (k < n)
        invariant 0 <= k <= n
        invariant sum == k * (2 * k - 1) * (2 * k + 1) / 3
        invariant i == 2 * k + 1
        decreases k
    {
        sum := sum + i * i;
        i := i + 2;
        k := k + 1;
    }
}

method FindMax_Correct(a: array<int>) returns (r: int)
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
        decreases a.Length - i
    {
        if (a[i] > r) { r := a[i]; }
        i := i + 1;
    }
}

method FindMax_Incorrect(a: array<int>) returns (r: int)
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
        decreases i
    {
        if (a[i] > r) { r := a[i]; }
        i := i + 1;
    }
}

method ReverseUptoK_Correct(s_in: array<int>, k: int) returns (s: array<int>)
    requires 2 <= k <= s_in.Length
    ensures forall i :: 0 <= i < k ==> s[i] == s_in[k - 1 - i]
    ensures forall i :: k <= i < s.Length ==> s[i] == s_in[i]
{
    var l : int := k - 1;
    var i : int := 0;
    var tmp : int;
    s := s_in;

    while (i < l - i)
        invariant 0 <= i <= (l + 1) / 2
        invariant forall p :: (0 <= p < i) || (l - i < p <= l) ==> s[p] == s_in[l - p]
        invariant forall p :: i <= p <= l - i ==> s[p] == s_in[p]
        invariant forall p :: k <= p < s.Length ==> s[p] == s_in[p]
        invariant 2 <= k <= s.Length
        invariant l == k - 1
        decreases l - i
    {
        tmp := s[i];
        s[i] := s[l - i];
        s[l - i] := tmp;
        i := i + 1;
    }
}

method ReverseUptoK_Incorrect(s_in: array<int>, k: int) returns (s: array<int>)
    requires 2 <= k <= s_in.Length
    ensures forall i :: 0 <= i < k ==> s[i] == s_in[k - 1 - i]
    ensures forall i :: k <= i < s.Length ==> s[i] == s_in[i]
{
    var l : int := k - 1;
    var i : int := 0;
    var tmp : int;
    s := s_in;

    while (i < l - i)
        invariant 0 <= i <= (l + 1) / 2
        invariant forall p :: (0 <= p < i) || (l - i < p <= l) ==> s[p] == s_in[l - p]
        invariant forall p :: i <= p <= l - i ==> s[p] == s_in[p]
        invariant forall p :: k <= p < s.Length ==> s[p] == s_in[p]
        invariant 2 <= k <= s.Length
        invariant l == k - 1
        decreases i
    {
        tmp := s[i];
        s[i] := s[l - i];
        s[l - i] := tmp;
        i := i + 1;
    }
}

method InvertArray_Correct(a0: array<int>) returns (a: array<int>)
    requires 0 <= a0.Length <= 10
    ensures forall i :: 0 <= i < a.Length ==> a[i] == a0[a.Length - 1 - i]
    ensures a.Length == a0.Length
{
    var index : int := 0;
    a := a0;

    while (index < a.Length / 2)
        invariant 0 <= index <= a.Length / 2
        invariant forall i :: 0 <= i < index ==> a[i] == a0[a.Length - 1 - i]
        invariant forall i :: 0 <= i < index ==> a[a.Length - 1 - i] == a0[i]
        invariant forall i :: index <= i < a.Length - index ==> a[i] == a0[i]
        invariant 0 <= a0.Length <= 10
        invariant a.Length == a0.Length
        decreases a.Length / 2 - index
    {
        a[index], a[a.Length - 1 - index] := a[a.Length - 1 - index], a[index];
        index := index + 1;
    }
}

method InvertArray_Incorrect(a0: array<int>) returns (a: array<int>)
    requires 0 <= a0.Length <= 10
    ensures forall i :: 0 <= i < a.Length ==> a[i] == a0[a.Length - 1 - i]
    ensures a.Length == a0.Length
{
    var index : int := 0;
    a := a0;

    while (index < a.Length / 2)
        invariant 0 <= index <= a.Length / 2
        invariant forall i :: 0 <= i < index ==> a[i] == a0[a.Length - 1 - i]
        invariant forall i :: 0 <= i < index ==> a[a.Length - 1 - i] == a0[i]
        invariant forall i :: index <= i < a.Length - index ==> a[i] == a0[i]
        invariant 0 <= a0.Length <= 10
        invariant a.Length == a0.Length
        decreases index
    {
        a[index], a[a.Length - 1 - index] := a[a.Length - 1 - index], a[index];
        index := index + 1;
    }
}


