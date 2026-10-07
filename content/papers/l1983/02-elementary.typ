#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== Элементарные матрицы и основные автоморфизмы
<sec:l1983-elementary>

Матрицы $x epsilon_(i j)$ ($x in K$, $i > j$), где $epsilon_(i j)$ — матричная
единица, называются элементарными. Они порождают аддитивную и присоединенную
группы кольца $NT(n, K)$, причем

#source(3, printed: 65)$
  (x epsilon_(i j))(y epsilon_(k m)) = cases(
    x y epsilon_(i m)\, & j = k,
    0\, & j != k,
  )
$ <eq:l1983-elementary-product>
$
  x epsilon_(i j) ast y epsilon_(k m) = cases(
    x y epsilon_(i m)\, & i > j = k > m,
    0\, & i != m\, j != k,
    -y x epsilon_(k j)\, & k > m = i > j,
  )
$ <eq:l1983-elementary-lie-product>
$
  [x epsilon_(i j), y epsilon_(k m)] = cases(
    x y epsilon_(i m)\, & i > j = k > m,
    0\, & i != m\, j != k,
    -y x epsilon_(k j)\, & k > m = i > j,
  )
$ <eq:l1983-elementary-commutator>
$
  x epsilon_(i j) compose y epsilon_(i j) = (x + y) epsilon_(i j),
  quad i > j quad (x, y in K).
$ <eq:l1983-elementary-addition>

#lemma[
  Автоморфизмами кольца $NT(n, K)$ (автоморфизмами ассоциированного кольца Ли)
  являются те и только те автоморфизмы его аддитивной группы, которые сохраняют
  соотношения @eq:l1983-elementary-product (соответственно соотношения
  @eq:l1983-elementary-lie-product).
] <lem:l1983-additive-extension>

#lemma[
  Всякое соотношение между элементами присоединенной группы кольца $NT(n, K)$
  является следствием соотношений между элементами кольца $K$ и соотношений
  @eq:l1983-elementary-commutator, @eq:l1983-elementary-addition.
] <lem:l1983-adjoint-presentation>

#proof[
  Произвольное соотношение в присоединенной группе записывается в виде $W = 0$,
  где $W = a_1 epsilon_(i_1 j_1) compose a_2 epsilon_(i_2 j_2)
  compose dots compose a_r epsilon_(i_r j_r)$. Групповое тождество
  $u compose v = v compose u compose [u^(-1), v^(-1)]$ и
  @eq:l1983-elementary-commutator, @eq:l1983-elementary-addition позволяют
  преобразовать $W$ к присоединенному произведению элементарных матриц
  $w_(i j) epsilon_(i j)$ ($i > j$), расположенных в соответствии с
  упорядочением $<$ индексов $(i, j)$:
  $(2, 1) < (3, 1) < (3, 2) < dots < (n, n - 2) < (n, n - 1)$. Отсюда
  $lr(‖w_(i j)‖) = 0$ (см. также лемму 1 [@bib:l1983-Levchuk1977]), и поэтому в
  кольце $K$ выполняются соотношения $w_(i j) lr((a_1, a_2, dots, a_r)) = 0$,
  $i > j$. Переход от $W$ к $lr(‖w_(i j)‖)$ обратим. Таким образом, соотношение
  $W = 0$ есть следствие указанных соотношений в кольце $K$ и соотношений
  @eq:l1983-elementary-commutator, @eq:l1983-elementary-addition.
]

Отметим, что в доказательстве не использовалось условие $1 in K$. Для конечного
простого поля $K$ лемма~@lem:l1983-adjoint-presentation равносильна теореме 2
[@bib:l1983-Pavlov1952]; см. также лемму 36 [@bib:l1983-Steinberg1975]. Из
леммы~@lem:l1983-adjoint-presentation (см. также [@bib:l1983-Kargapolov1977,
16.2.3]) вытекает

#lemma[
  Отображение элементарных матриц в $NT(n, K)$ допускает продолжение до
  эндоморфизма присоединенной группы, если оно сохраняет соотношения
  @eq:l1983-elementary-commutator, @eq:l1983-elementary-addition. Эндоморфизм
  есть автоморфизм, если он эпиморфен и индуцирует автоморфизм центра.
] <lem:l1983-adjoint-extension>

Через $Tc$, $D$ и $Jc$ обозначаем подгруппу сопряжений
$alpha arrow.r t^(-1) alpha t$ кольца $NT(n, K)$ соответственно треугольными,
диагональными и унитреугольными обратимыми матрицами над $K$. Ясно, что $Jc$ —
подгруппа внутренних автоморфизмов присоединенной группы. Подгруппу ее
центральных автоморфизмов обозначаем через $Zc$. Она порождается автоморфизмами
$zeta_i lr((lambda)): lr(‖a_(k m)‖) arrow.r lr(‖a_(k m)‖)
+ a_(i+1,i)^lambda epsilon_(n 1)$ кольца $NT(n, K)$ для всевозможных
$lambda in End(K^+)$, $1 <= i < n$. При этом
$(End(K^+))^+ tilde.eq Zc_i = {zeta_i lr((lambda)): lambda in End(K^+)}$
и $Zc = Zc_1 times Zc_2 times dots times Zc_(n-1)$.

Автоморфизмы $overline(pi)$ кольца $NT(n, K)$, индуцируемые автоморфизмами $pi$
кольца $K$, образуют подгруппу $AutK K$. Нам потребуется их обобщение.
$e$-автоморфизмом кольца $K$ назовем автоморфизм $theta$ его аддитивной группы
$K^+$, если $1^theta = 1$, $e$ — идемпотент центра кольца $K$ и $theta$
индуцирует изоморфизм подкольца $e K$ и антиизоморфизм подкольца $(1 - e) K$.
Сопоставим с ним отображение
$
  tau: x epsilon_(i j) arrow.r (e x)^theta epsilon_(i j)
  + (-1)^(i-j-1) (x - e x)^theta epsilon_(n-j+1,n-i+1),
  quad 1 <= j < i <= n\, x in K.
$
Соотношения @eq:l1983-elementary-lie-product–@eq:l1983-elementary-addition, а
также сложение на множествах $K epsilon_(i j)$ инвариантны относительно $tau$.
Леммы~@lem:l1983-additive-extension и @lem:l1983-adjoint-extension показывают,
что $tau$ допускает продолжения до автоморфизма лиева кольца $NT(n, K)$ и до
автоморфизма присоединенной группы. Построенные автоморфизмы будем называть
#source(4, printed: 66)идемпотентно-кольцевыми или, когда $theta$ —
тождественное преобразование кольца $K$ (и, следовательно, подкольцо $(1 - e) K$
коммутативно), идемпотентными автоморфизмами. Идемпотентно-кольцевые
(идемпотентные) автоморфизмы присоединенной группы образуют подгруппу $Phi$
(соответственно $W$); аналогично вводим подгруппы $Phi^ast$ и $W^ast$
автоморфизмов лиева кольца $NT(n, K)$. Когда кольцо $K$ коммутативно, очевидно,
имеем $Phi = W ⋋ AutK K$, $Phi^ast = W^ast ⋋ AutK K$.

Следующие автоморфизмы определим также образами элементарных матриц;
<pass:l1983-hypercentral-definitions>
если образ не указан, то элементарная матрица остается на месте. Во всех случаях
автоморфность отображения просто устанавливается с помощью
лемм~@lem:l1983-additive-extension и @lem:l1983-adjoint-extension.

Пусть элемент $a in K$ аннулирует слева множество $(K ast K) union {2}$, а
элемент $b in K$ — справа. Тогда отображения
$
  nu_a: x epsilon_21 arrow.r (epsilon_21 + a epsilon_(n 3)) x,
  quad x epsilon_31 arrow.r (epsilon_31 + a epsilon_(n 2)) x\, x in K,
$
$
  nu'_b: x epsilon_(n,n-1) arrow.r x(epsilon_(n,n-1) + b epsilon_(n-2,1)),
  quad x epsilon_(n,n-2) arrow.r x(epsilon_(n,n-2) + b epsilon_(n-1,1))\, x in K
$
определяют автоморфизмы лиева кольца $NT(n, K)$, $n >= 4$. Подгруппу,
порожденную автоморфизмами такого вида, обозначаем через $V^ast$. При $n > 5$
она, очевидно, изоморфна прямой сумме аддитивных групп левого и правого
аннуляторов множества $(K ast K) union {2}$ в кольце $K$. Далее, если элемент
$a$ удовлетворяет дополнительному условию $a(x^2 - x)(y^2 - y) = 0$
($x, y in K$), то ему соответствует автоморфизм
$
  eta_a: x epsilon_21 arrow.r (epsilon_21 + a epsilon_(n 3)) x,
  quad x epsilon_32 arrow.r x epsilon_32 + a(x^2 - x) epsilon_(n 2),
  x epsilon_31 arrow.r x epsilon_31 + a x epsilon_(n 2) + a x^2 epsilon_(n 1),
  quad x in K quad (n >= 4).
$
присоединенной группы. Симметрично записывается ее автоморфизм $eta'_b$ при
условии $(x^2 - x)(y^2 - y) b = 0$ ($x, y in K$). Подгруппа $V$ порождена
автоморфизмами вида $eta_a$ или $eta'_b$.

Отображение $x epsilon_21 arrow.r (epsilon_21 + a epsilon_(n 2)) x$, $x in K$,
при $a(K ast K) = 0$ сохраняет соотношения @eq:l1983-elementary-lie-product, и,
следовательно, его аддитивное продолжение на кольцо $NT(n, K)$, $n >= 3$,
является по лемме~@lem:l1983-additive-extension автоморфизмом ассоциированного
кольца Ли; аналогично $x epsilon_(n,n-1) arrow.r x(epsilon_(n,n-1)
  + b epsilon_(n-1,1))$, $x in K$, есть автоморфизм при $(K ast K)b = 0$.
Подгруппа $Uc^ast$, порожденная всевозможными автоморфизмами такого вида, при
$n > 3$, очевидно, изоморфна прямой сумме аддитивных групп левого и правого
аннуляторов множества $K ast K$ в кольце $K$.

Пусть $lambda$ — преобразование кольца $K$, $a in K$. По
лемме~@lem:l1983-adjoint-extension отображение
$sigma_lambda: x epsilon_21 arrow.r x epsilon_21 + a x epsilon_(n 2)
+ x^lambda epsilon_(n 1)$, $x in K$ (аналогично
$sigma'_lambda: x epsilon_(n,n-1) arrow.r x epsilon_(n,n-1)
+ x a epsilon_(n-1,1) + x^lambda epsilon_(n 1)$, $x in K$) допускает продолжение
до автоморфизма присоединенной группы кольца $NT(n, K)$, $n >= 3$, в том и
только в том случае, когда элемент $(x + y)^lambda - x^lambda - y^lambda$ при
любых $x, y in K$ равен $a x y$ (соответственно $x y a$) и, в частности,
$a = 2^lambda - 2(1^lambda)$. Подгруппа, порожденная всевозможными
автоморфизмами вида $sigma_lambda$ или $sigma'_lambda$, обозначается через
$Uc^((c))$.
