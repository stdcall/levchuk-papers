#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": NT, proposition

#heading(level: 3, numbering: none)[Введение] <sec:l1987-rings-introduction>

#source(2, printed: 631) Всюду в дальнейшем $Gamma$ есть цепь (линейно
упорядоченное множество), $K$ — ассоциативное кольцо. Кольцо $NT(Gamma, K)$ (при
$Gamma = {1, 2, dots, n}$ также пишут $NT(n, K)$), аддитивно порождаемое
элементами $x epsilon_(i j)$ ($x in K$, $i, j in Gamma$, $i > j$),
подчиняющимися обычным правилам сложения и умножения элементарных матриц,
локально нильпотентно и, следовательно, радикально. Продолжая
[@bib:l1987-rings-Levchuk1975; @bib:l1987-rings-Levchuk1976;
@bib:l1987-rings-Levchuk1983], мы исследуем структурные связи и автоморфизмы
кольца $R = NT(Gamma, K)$, его присоединенной группы $cal(G)(R)$ и
ассоциированного кольца Ли $Lambda(R)$.

Для элемента из $NT(Gamma, K)$ используем обычную матричную запись $‖a_(u v)‖$
($Gamma$-матрица), называя $a_(u v)$ его $(u, v)$-координатой. Пишем $i ◁ j$,
если $i$ — предшественник $j$ [@bib:l1987-rings-Kuratowski1970, с. 215], и
$i ≪ j$, если $i < j$, $i ◁̸ j$. Первый и последний элементы $Gamma$ (если они
существуют) обозначаются соответственно $p$ и $q$.

=== <sec:l1987-rings-normal-subgroups>

В теореме @th:l1976-normal-lie-correspondence [@bib:l1987-rings-Levchuk1976]
устанавливается соответствие между нормальными подгруппами $cal(G)(R)$ и
идеалами $Lambda(R)$, $R = NT(Gamma, K)$, где $Gamma$ — конечная цепь; см. также
[@bib:l1987-rings-Levchuk1979]. Ее доказательство легко распространяется и на
случай произвольной цепи $Gamma$. По определению, ковровое подкольцо
$R(frak(A))$ кольца $NT(Gamma, K)$ порождается подмножествами
$frak(A)_(i j) epsilon_(i j)$ ($i, j in Gamma$, $i > j$), где $frak(A)_(i j)$ —
аддитивные подгруппы кольца $K$ с условием
$frak(A)_(i k) frak(A)_(k j) subset frak(A)_(i j)$ ($i > k > j$).

#theorem[Для произвольного коврового подкольца $R = R(frak(A))$ кольца
  $NT(Gamma, K)$ выполняются следующие утверждения:

  #enum(
    numbering: "1)",
    [#source(3, printed: 632) условие нормальности подгруппы группы $cal(G)(R)$
      равносильно тому, что она является идеалом группоида $R$ относительно
      лиева умножения $*$ ($alpha * beta = alpha beta - beta alpha$);],
    [класс максимальных абелевых нормальных подгрупп группы $cal(G)(R)$
      совпадает с классом максимальных абелевых идеалов лиева кольца
      $Lambda(R)$;],
    [класс всех нормальных подгрупп группы $cal(G)(R)$ совпадает с классом всех
      идеалов лиева кольца $Lambda(R)$, если выполнено условие

      $
        frak(A)_(i j) = frak(A)'_(i j)
        + (frak(A)_(i j) inter J_j lr((frak(A)))) = frak(A)'_(i j)
        + (frak(A)_(i j) inter I_i lr((frak(A)))), quad j ≪ i,
      $ <eq:l1987-rings-carpet-annihilators>

      где $J_j lr((frak(A)))$ — левый аннулятор множества
      $union_(m<j) frak(A)_(j m)$, а $I_i lr((frak(A)))$ — правый аннулятор
      множества $union_(k>i) frak(A)_(k i)$ в кольце $K$, $frak(A)'_(i j)$ —
      аддитивная подгруппа, порожденная множествами
      $frak(A)_(i l) frak(A)_(l j)$, $j < l < i$.],
  )] <th:l1987-rings-normal-lie>

#proof[Заметим, что для любого конечного множества $M subset NT(Gamma, K)$
  множество $Gamma_1 subset Gamma$ всех индексов элементарных матриц
  $x epsilon_(i j)$, участвующих в разложении элементов из $M$, конечно и
  $M subset NT(Gamma_1, K)$. Поэтому для доказательства теоремы достаточно
  установить справедливость утверждений 1)–3) для
  $R = R(frak(A)) inter NT(Gamma_1, K)$ при любом конечном подмножестве
  $Gamma_1 subset Gamma$. Зафиксируем $Gamma_1$. Леммы
  @lem:l1976-elementary-generators–@lem:l1976-abelian-annihilator
  [@bib:l1987-rings-Levchuk1976] остаются справедливыми вместе с
  доказательствами, если заменить в них $NT(n, K)$ на
  $R(frak(A)) inter NT(Gamma_1, K)$ и для элементов $x epsilon_(i j)$ требовать
  включение $x in frak(A)_(i j)$. Поэтому утверждения 1), 2) для
  $R = R(frak(A)) inter NT(Gamma_1, K)$ выполняются, а для доказательства 3),
  как и в [@bib:l1987-rings-Levchuk1976, с. 564;
  @pass:l1976-lie-products[доказательство теоремы]], остается показать, что при
  любых $alpha = ‖a_(k m)‖$,
  $beta = ‖b_(k m)‖ in R(frak(A)) inter NT(Gamma_1, K)$ идеал $M(alpha, beta)$
  лиева кольца $Lambda(R(frak(A)))$, порожденный множеством
  ${alpha, beta} * R(frak(A))$, содержит $(a_(i j) epsilon_(i j)) beta$ и
  $alpha (b_(i j) epsilon_(i j))$, $j ≪ i$. В силу
  @eq:l1987-rings-carpet-annihilators
  $a_(i j) epsilon_(i j) beta = a'_(i j) epsilon_(i j) beta$, где
  $a'_(i j) in frak(A)'_(i j)$ и, следовательно,
  $a'_(i j) in sum_(m=1)^r frak(A)_(i l_m) frak(A)_(l_m j)$ для некоторых
  $l_1, l_2, dots, l_r in Gamma$, $j < l_m < i$. Поэтому существуют
  $x_m in frak(A)_(i l_m)$, $y_m in frak(A)_(l_m j)$ такие, что
  $a'_(i j) = x_1 y_1 + x_2 y_2 + dots + x_r y_r$. Отсюда

  $
    a_(i j) epsilon_(i j) beta = sum_(m=1)^r x_m y_m epsilon_(i j) beta
    = sum_(m=1)^r x_m epsilon_(i l_m) * (y_m epsilon_(l_m j) * beta)
    in M(alpha, beta).
  $

  Аналогично, $alpha (b_(i j) epsilon_(i j)) in M(alpha, beta)$, $j ≪ i$.
  Теорема доказана.]

#corollary[#source(4, printed: 633) Если подмножество ${x y | x, y in K}$
  порождает кольцо $K$ (кратко: $K = K^2$); в частности, если $1 in K$, то класс
  нормальных подгрупп присоединенной группы кольца $NT(Gamma, K)$ совпадает с
  классом всех идеалов ассоциированного кольца Ли.] <cor:l1987-rings-unital>

Ограничение на кольцо $K$ в следствии нельзя отбросить, как показывает пример
@exm:l1976-even-ring [@bib:l1987-rings-Levchuk1976]. Пример Е. И. Хухро (см.
ответ на вопрос 6.19 [@bib:l1987-rings-Kourovka1980]) показывает, что теорема
@th:l1987-rings-normal-lie, 1) не переносится на произвольное нильпотентное
ассоциативное кольцо $R$.

#remark[Кольцо $NT(Gamma, K)$ можно рассматривать как сжатое полугрупповое
  кольцо над $K$ мультипликативной полугруппы $T union {0}$,
  $T = {epsilon_(i j) | i, j in Gamma, i > j}$; см. также
  [@bib:l1987-rings-Clifford1972, § 5.2]. В доказательстве теоремы
  @th:l1987-rings-normal-lie, 1) мы использовали лишь следующие свойства $T$:

  #enum(
    numbering: ru-enum,
    [если $c_1, c_2, dots, c_r in T$ ($r > 1$), $c_i c_(i+1) != 0$
      ($1 <= i < r$), то $c_r c_1 = 0$;],
    [если $c a, c b in T$ (или $a c, b c in T$), то существует и единствен
      элемент $d in T union {1}$ такой, что $a = b d$ или $b = a d$
      (соответственно $a = d b$ или $b = d a$).],
  )

  С другой стороны, полугруппы вида ${epsilon_(i j) | i, j in Gamma, i > j}$ и
  их гомоморфные образы не исчерпывают всех полугрупп $T union {0}$ с условиями
  а), б).] <rem:l1987-rings-semigroup>

=== <sec:l1987-rings-ideals>

Пусть $H$ — идеал лиева кольца $Lambda(NT(Gamma, K))$ над телом $K$.
Совокупность $(k, m)$-координат всех его элементов обозначаем через $H_(k m)$.
Позицию $(i, j)$ называем углом $H$, если $H_(i j) != 0$ и $H_(k m) = 0$ для
всех $(k, m) != (i, j)$, $j <= m < k <= i$. Замечая, что
$K epsilon_(i j) * (H * K epsilon_(k m))$ совпадает с
$K(H_(j k)) K epsilon_(i m)$, $(K K) epsilon_(i m) H$ или
$H(K K) epsilon_(k j)$, соответственно случаям $i > j > k > m$, $i > j = k > m$,
$k > m = i > j$ получаем, как и в [@bib:l1987-rings-Levchuk1976, §
@sec:l1976-correspondence]:

#enum(
  numbering: n => if n == 1 { "А)" } else { "Б)" },
  [при $H_(i j) != 0$ имеем $K epsilon_(k m) subset H$ для всех
    $(k, m) != (i, j)$, $m <= j < i <= k$, исключая, быть может, когда $(i, j)$
    — угол $H$, позицию $(k, j)$, $i ◁ k$, если $H$ имеет угол в $k$-м столбце,
    и позицию $(i, m)$, $m ◁ j$, если в $m$-й строке есть угол $H$;],
  [если $(s, m)$ и $(i, j)$ — углы $H$, $i ◁ m$, то либо
    $phi : a_(i j) arrow.r a_(s m)$ ($‖a_(u v)‖ in H$) есть изоморфизм
    аддитивной группы $H_(i j)$ на $H_(s m)$ и
    $H supset {x a epsilon_(m j) - a^phi x epsilon_(s i) |
      x in K, a in H_(i j)}$, либо
    $H supset K epsilon_(s i) + K epsilon_(m j)$.],
)

Отсюда легко вытекает

#proposition[Идеалами кольца $NT(Gamma, K)$ над телом $K$ (идеалами
  ассоциированного кольца Ли) являются те и только те его аддитивные подгруппы
  $H$, которые #source(5, printed: 634) удовлетворяют условию

  $
    Q_(i j) = 〈K epsilon_(u v) | v <= j < i <= u, (u, v) != (i, j)〉
    subset H "при" H_(i j) != 0 quad (i, j in Gamma, i > j)
  $

  (соответственно условиям А), Б)).] <prop:l1987-rings-ideal-criterion>

#corollary[Если $Gamma$ — плотная цепь, то класс идеалов кольца $NT(Gamma, K)$
  над телом $K$ совпадает с классом идеалов ассоциированного кольца
  Ли.] <cor:l1987-rings-dense>

И. Д. Адо [@bib:l1987-rings-Ado1943] указал пример $p$-группы, совпадающей с
коммутантом, используя группу $cal(G)(NT(Gamma, GF(p)))$, где $Gamma$ —
множество рациональных чисел отрезка $[0,1]$. (Конечно, в качестве $Gamma$ можно
брать любую плотную цепь.)

=== <sec:l1987-rings-abelian>

Произвольный максимальный абелев идеал $M$ кольца $Lambda(R)$,
$R = NT(Gamma, K)$, в случае первичного кольца $K$ допускает явную запись по
аналогии с [@bib:l1987-rings-Levchuk1976, лемма @lem:l1976-prime-abelian]. Через
$S$ и $T$ обозначим совокупность элементов $i in Gamma$, для которых можно
выбрать $k in Gamma$ так, что $M_(i k) != 0$ или соответственно $M_(k i) != 0$.
Ясно, что $T$ и $overline(S) = Gamma without S$ — отрезки в $Gamma$
[@bib:l1987-rings-Kuratowski1970, с. 215] и $M$ лежит в идеале

$ N_(S T) = 〈K epsilon_(u v) | u in S, v in T, u > v〉. $

При $S inter T = emptyset$ имеем $M = N_(overline(T) T)$, так как
$N_(overline(T) T)$ — абелев идеал. Допустим, что $S inter T$ — непустое
множество и $D$ — его произвольное конечное подмножество. Мы можем выбрать
конечное множество $M' subset M$ так, что при любом $d in D$ найдутся
$k, l in Gamma$ с условием $M_(k d) != 0$, $M_(d l) != 0$. Пусть $Gamma_1$ —
произвольное конечное подмножество $Gamma$, содержащее все индексы элементарных
матриц, участвующих в разложениях элементов из $M'$. Абелев идеал $M inter R_1$
кольца $Lambda(R_1)$, $R_1 = NT(Gamma_1, K)$, содержит $M'$ и, как показано в
лемме @lem:l1976-prime-abelian [@bib:l1987-rings-Levchuk1976], лежит в множестве
вида @eq:l1976-prime-abelian или @eq:l1976-prime-lie-abelian
[@bib:l1987-rings-Levchuk1976]; в частности, $|D| <= 2$. В силу произвола в
выборе $D$ и $Gamma_1$ цепь $Gamma$ должна иметь первый и последний элементы (их
обозначаем соответственно $p$ и $q$) и $|S inter T| <= 2$, причем равенство
может достигаться лишь при $2K = 0$. Ограничиваясь случаем кольца $K$ без
делителей нуля, получаем, что $M$ совпадает с одним из следующих множеств:

$
  M_i lr((frak(M))) = 〈K epsilon_(u v) | v < i < u〉
  + {a epsilon_(i p) + b epsilon_(q i) | a, b in frak(M)}, quad p < i < q,
$

$
  M_(i j)(frak(N)) = 〈K epsilon_(u v) | v < i < j < u〉
  + {a_(11) epsilon_(i p) + a_(12) epsilon_(j p) + a_(21) epsilon_(q i)
    + a_(22) epsilon_(q j) | ‖a_(k l)‖ in frak(N)},
$

#source(6, printed: 635) $p < i ◁ j < q$, где $frak(M)$ и $frak(N)$ есть
определенные аддитивные подгруппы соответственно $1 times 2$- и
$2 times 2$-матриц над $K$ с ненулевыми $frak(M)_(1 t)$, $frak(N)_(s t)$
($t = 1, 2$; $s = 1, 2$). По доказанному, любой абелев идеал ассоциированного
кольца Ли лежит в одном из множеств $N_(overline(T) T)$, $M_i lr((frak(M)))$,
$M_(i j)(frak(N))$. Кроме того, $N_(overline(T) T)$ и $M_i lr((frak(M)))$ —
идеалы кольца $NT(Gamma, K)$. Отсюда вытекает

#theorem[Пусть $K$ — кольцо без делителей нуля. Максимальный абелев идеал кольца
  $R = NT(Gamma, K)$ совпадает либо с $N_(overline(T) T)$ для некоторого отрезка
  $T$ цепи $Gamma$, $T != emptyset, Gamma$, либо с $M_i lr((frak(M)))$,
  $p < i < q$. Максимальный абелев идеал кольца $Lambda(R)$ либо является
  идеалом кольца $R$, либо $2K = 0$ и он совпадает с $M_(i j)(frak(N))$,
  $p < i ◁ j < q$. (Описание множеств $frak(M)$ и $frak(N)$, при которых
  $M_i lr((frak(M)))$ и $M_(i j)(frak(N))$ есть максимальные абелевы идеалы,
  дано в [@bib:l1987-rings-Levchuk1976, леммы @lem:l1976-domain-abelian и
  @lem:l1976-domain-lie-exceptional].)] <th:l1987-rings-maximal-abelian>

Распространяя доказательства леммы @lem:l1976-prime-abelian
[@bib:l1987-rings-Levchuk1976] и теоремы @th:l1987-rings-maximal-abelian на
ковровые подкольца, получаем

#proposition[Пусть $R(frak(A))$ — ковровое подкольцо кольца $NT(Gamma, K)$ над
  кольцом $K$ без делителей нуля, причем $frak(A)_(i j) != 0$ ($i, j in Gamma$,
  $i > j$). Тогда любой максимальный абелев идеал кольца $Lambda(R(frak(A)))$
  является пересечением $R(frak(A))$ и подходящего максимального абелева идеала
  кольца $Lambda(NT(Gamma, K))$.] <prop:l1987-rings-carpet-abelian>
