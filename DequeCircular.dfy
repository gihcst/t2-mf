// Integrantes: Giovanna Cruz Castro, Eduarda dos Santos Patricio

class DequeCircular {
  // --- Representação Concreta (Fila Circular Clássica com Head e Tail) ---
  var arr: array<int>
  var head: int // Índice do primeiro elemento
  var tail: int // Índice da próxima posição livre no final

  // --- Representação Abstrata (Ghost) ---
  ghost var Conteudo: seq<int>
  ghost var Repr: set<object>

  // Função auxiliar ghost para calcular a quantidade de elementos a partir de head e tail
  ghost function TamanhoLogico(): int
    reads this, arr
    requires arr.Length > 0
    requires 0 <= head < arr.Length && 0 <= tail < arr.Length
  {
    if tail >= head then tail - head
    else arr.Length - head + tail
  }

  // --- Invariante de Classe ---
  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    arr in Repr &&
    arr.Length >= 2 && // Capacidade mínima 1 + 1 posição sentinela
    0 <= head < arr.Length &&
    0 <= tail < arr.Length &&
    |Conteudo| == TamanhoLogico() &&
    |Conteudo| <= arr.Length - 1 &&
    forall i :: 0 <= i < |Conteudo| ==> Conteudo[i] == arr[(head + i) % arr.Length]
  }

  // --- Construtor ---
  constructor (capacidade: int)
    requires capacidade > 0
    ensures Valid()
    ensures fresh(Repr)
    ensures Conteudo == []
    ensures Capacidade() == capacidade
  {
    arr := new int[capacidade + 1]; // +1 posição sentinela para distinguir vazio de cheio
    head := 0;
    tail := 0;
    Conteudo := [];
    Repr := {this, arr};
  }

  // --- Operações de Consulta ---

  function Capacidade(): int
    reads this, Repr
    requires Valid()
    ensures Capacidade() == arr.Length - 1
  {
    arr.Length - 1
  }

  function Tamanho(): int
    reads this, Repr
    requires Valid()
    ensures Tamanho() == |Conteudo|
  {
    if tail >= head then tail - head
    else arr.Length - head + tail
  }

  function EstaVazio(): bool
    reads this, Repr
    requires Valid()
    ensures EstaVazio() <==> |Conteudo| == 0
  {
    head == tail
  }

  function EstaCheio(): bool
    reads this, Repr
    requires Valid()
    ensures EstaCheio() <==> |Conteudo| == Capacidade()
  {
    (tail + 1) % arr.Length == head
  }

  method Contem(x: int) returns (encontrado: bool)
    requires Valid()
    ensures encontrado <==> x in Conteudo
  {
    var n := Tamanho();
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall j :: 0 <= j < i ==> Conteudo[j] != x
      decreases n - i
    {
      if arr[(head + i) % arr.Length] == x {
        assert Conteudo[i] == x;
        return true;
      }
      i := i + 1;
    }
    return false;
  }

  // --- Operações de Inserção e Remoção ---

  method AdicionarFim(x: int)
    requires Valid()
    requires !EstaCheio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures Conteudo == old(Conteudo) + [x]
  {
    arr[tail] := x;
    tail := (tail + 1) % arr.Length;
    Conteudo := Conteudo + [x];
  }

  method AdicionarInicio(x: int)
    requires Valid()
    requires !EstaCheio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures Conteudo == [x] + old(Conteudo)
  {
    var oldHead := head;
    var oldConteudo := Conteudo;
    var novoHead := if head > 0 then head - 1 else arr.Length - 1;
    head := novoHead;
    arr[head] := x;
    Conteudo := [x] + Conteudo;

    // Prova construtiva para cada posição i do novo Conteudo
    forall i | 0 <= i < |Conteudo|
      ensures Conteudo[i] == arr[(head + i) % arr.Length]
    {
      if i == 0 {
        assert (head + 0) % arr.Length == head;
      } else {
        assert (head + i) % arr.Length == (oldHead + (i - 1)) % arr.Length;
        assert oldConteudo[i - 1] == arr[(oldHead + (i - 1)) % arr.Length];
      }
    }
  }

  method RemoverInicio() returns (x: int)
    requires Valid()
    requires !EstaVazio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures x == old(Conteudo)[0]
    ensures Conteudo == old(Conteudo)[1..]
  {
    x := arr[head];
    head := (head + 1) % arr.Length;
    Conteudo := Conteudo[1..];
  }

  method RemoverFim() returns (x: int)
    requires Valid()
    requires !EstaVazio()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == old(Capacidade())
    ensures x == old(Conteudo)[|old(Conteudo)| - 1]
    ensures Conteudo == old(Conteudo)[..|old(Conteudo)| - 1]
  {
    var novoTail := if tail > 0 then tail - 1 else arr.Length - 1;
    assert novoTail == (tail - 1 + arr.Length) % arr.Length;
    assert novoTail == (head + |Conteudo| - 1) % arr.Length;
    tail := novoTail;
    x := arr[tail];
    Conteudo := Conteudo[..|Conteudo| - 1];
  }

  // --- Operação de Redimensionamento ---

  method Redimensionar(novaCapacidade: int)
    requires Valid()
    requires novaCapacidade > Capacidade()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Capacidade() == novaCapacidade
    ensures Conteudo == old(Conteudo)
  {
    var n := Tamanho();
    var oldArr := arr;
    var oldHead := head;
    var oldConteudo := Conteudo;
    var novoArr := new int[novaCapacidade + 1];
    var i := 0;

    while i < n
      modifies novoArr
      invariant Conteudo == oldConteudo
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> novoArr[k] == oldConteudo[k]
      decreases n - i
    {
      assert oldConteudo[i] == oldArr[(oldHead + i) % oldArr.Length];
      novoArr[i] := oldArr[(oldHead + i) % oldArr.Length];
      i := i + 1;
    }

    arr := novoArr;
    head := 0;
    tail := n;
    Repr := {this, arr};
  }
}

// --- Método Main com Testes Unitários ---
method Main() {
  var dq := new DequeCircular(3);
  assert dq.EstaVazio();
  assert !dq.EstaCheio();
  assert dq.Tamanho() == 0;
  assert dq.Capacidade() == 3;
  assert dq.Conteudo == [];

  // Inserções no fim e no início (forçando circularidade do índice head)
  dq.AdicionarFim(10);
  assert dq.Conteudo == [10];

  dq.AdicionarInicio(5);
  assert dq.Conteudo == [5, 10];

  dq.AdicionarFim(20);
  assert dq.Conteudo == [5, 10, 20];
  assert dq.EstaCheio();
  assert dq.Tamanho() == 3;

  // Busca de elementos
  var tem10 := dq.Contem(10);
  assert tem10;
  var tem99 := dq.Contem(99);
  assert !tem99;

  // Remoções nas duas extremidades
  var ini := dq.RemoverInicio();
  assert ini == 5;
  assert dq.Conteudo == [10, 20];

  var fim := dq.RemoverFim();
  assert fim == 20;
  assert dq.Conteudo == [10];
  assert !dq.EstaVazio();

  // Redimensionamento para capacidade maior
  dq.Redimensionar(5);
  assert dq.Capacidade() == 5;
  assert dq.Tamanho() == 1;
  assert dq.Conteudo == [10];
  assert !dq.EstaCheio();

  // Novas inserções após redimensionar
  dq.AdicionarInicio(1);
  dq.AdicionarFim(30);
  dq.AdicionarFim(40);
  assert dq.Conteudo == [1, 10, 30, 40];
  assert dq.Tamanho() == 4;

  print "Todos os testes unitarios passaram com sucesso!\n";
}