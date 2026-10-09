#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== Основная теорема <sec:l1983-main-theorem>

Далее через $Gc_n lr((K))$ обозначается группа автоморфизмов присоединенной
группы кольца $NT(n, K)$, а через $Lambda_n lr((K))$ — группа автоморфизмов
ассоциированного кольца Ли. В этом параграфе доказывается

#theorem[
  Группа автоморфизмов кольца $NT(n, K)$, $n >= 3$, разложима в произведение
  $Zc Tc AutK K$ и совпадает с пересечением
  $Gc_n lr((K)) inter Lambda_n lr((K))$. При $n > 4$ справедливы равенства
  $Gc_n lr((K)) = Zc Uc^((c)) V Tc Phi$,
  $Lambda_n lr((K)) = Zc Uc^ast V^ast Tc Phi^ast$; они верны и при $n = 4$, если
  аннулятор элемента 2 в кольце $K$ нулевой или если $K$ — некоммутативное
  кольцо без делителей нуля.
] <th:l1983-main-automorphisms>

#source(5, printed: 67)Следующая лемма характеризует пирсовские разложения
ассоциативного кольца; их определения см., например, в
[@bib:l1983-Jacobson1961].

#lemma[
  Пусть кольцо $K$ представлено двумя способами в виде суммы непустых
  подмножеств: $K = A_1 + A_2 = A'_1 + A'_2$, причем $A'_1 A_1 = A'_2 A_2 = 0$.
  Тогда $K$ содержит идемпотент $e$ такой, что $A_1 = e K$, $A_2 = (1 - e) K$,
  $A'_1 = K(1 - e)$, $A'_2 = K e$. Идемпотент $e$ лежит в центре кольца $K$,
  если $e K = K e$.
] <lem:l1983-peirce-decomposition>

#proof[
  По условию $1 = e_1 + e_2 = e'_1 + e'_2$ для некоторых элементов $e_i in A_i$,
  $e'_i in A'_i$. Они удовлетворяют равенствам
  $
    e'_1 = e'_1(e_1 + e_2) = e'_1 e_2 = (e'_1 + e'_2)e_2 = e_2,
    quad e'_2 = e_1,
  $
  $
    e_1 - e_1^2 = e_1(1 - e_1) = e_1 e_2 = e'_2 e_2 = 0,
  $
  и, следовательно, $e_1$ — идемпотент. Кроме того,
  $
    A_i = (e'_1 + e'_2)A_i = (1 - e'_i)A_i = e_i A_i,
    quad i = 1, 2.
  $
  Так как сумма $e_1 K + (1 - e_1)K = K$ — прямая [@bib:l1983-Jacobson1961, с.
  77], то $A_i = e_i K$, $i = 1, 2$. Аналогично $A'_i = K(1 - e_i)$. Таким
  образом, первое утверждение леммы выполняется при $e = e_1$. Пусть $e K = K e$
  и $x in K$. Тогда $y e = e x$, $x e = e z$ для некоторых элементов
  $y, z in K$. Отсюда $e x = (y e)e = e x e = e(e z) = x e$, т. е. $e$ —
  центральный идемпотент. Лемма доказана.
]

При $1 <= j < n$, $1 < i <= n$ обозначим через $N_(i j)$ совокупность матриц из
$NT(n, K)$, у которых в столбцах с номерами $> j$ и в строках с номерами $< i$
стоят нули. В силу @eq:l1983-elementary-lie-product,
@eq:l1983-elementary-commutator множества
$
  Gamma_k = N_(k+1,1) + N_(k+2,2) + dots + N_(n,n-k)
  quad (k = 1, 2, dots, n - 1), quad Gamma_n = 0,
$
образуют нижний (одновременно верхний) центральный ряд как в присоединенной
группе кольца $NT(n, K)$, так и в ассоциированном кольце Ли. Заметим также, что
$N_(i j)$ при $i > j$ есть пересечение левого аннулятора $N_(2 j)$ идеала
$Gamma_j$ с правым аннулятором $N_(i,n-1)$ идеала $Gamma_(n-i)$ в кольце
$NT(n, K)$, где $Gamma_0 = NT(n, K)$. Отсюда вытекает (см. также лемму
@lem:l1976-centralizers [@bib:l1983-Levchuk1976Article])

#lemma[
  Множества $Gamma_k$ и их централизаторы
  $
    C(Gamma_k) = C(N_(k+1,n-k)) = N_(n-k+1,k), quad 1 <= k < n,
  $
  являются характеристическими в присоединенной группе кольца $NT(n, K)$, а
  также в ассоциированном кольце Ли. Идеалы $N_(i j)$ ($1 <= j < n$,
  $1 < i <= n$) являются характеристическими в кольце $NT(n, K)$, причем
  $C(N_(i j)) = N_(j+1,i-1)$.
] <lem:l1983-characteristic-centralizers>

#lemma[
  Пусть $n >= 5$ и $phi in Gc_n lr((K)) union Lambda_n lr((K))$. Тогда
  $
    N_(i+1,i)^phi = e N_(i+1,i) + (1 - e)N_(n-i+1,n-i),
    quad i = 2, 3, dots, n - 2,
  $
  для некоторого центрального идемпотента $e$ кольца $K$. По модулю
  $N_(n 3) + N_(n-2,1)$ эти равенства верны и при $i = 1$, $n - 1$. В частном
  случае, когда $e = 1$, существуют элементы $a, b, c, d in K$ такие, что
  $
    N_21^phi = (epsilon_21 + a epsilon_(n 3) + b epsilon_(n 2)) K
    + (epsilon_31 + a epsilon_(n 2)) K + N_41,
  $
  $
    N_(n,n-1)^phi = K(epsilon_(n,n-1) + c epsilon_(n-2,1)
      + d epsilon_(n-1,1)) + K(epsilon_(n,n-2) + c epsilon_(n-1,1))
    + N_(n,n-3),
  $
  $
    2 a = 2 c = 0, quad a(K ast K) = b(K ast K)
    = (K ast K)c = (K ast K)d = 0.
  $
] <lem:l1983-images-maximal-abelian>

#proof[
  В силу теоремы @th:l1976-normal-lie-correspondence
  [@bib:l1983-Levchuk1976Article] и леммы~@lem:l1983-characteristic-centralizers
  множества $N_(i+1,i)$ и $N_(i+1,i)^phi = H^((i))$ ($1 <= i < n$) являются
  максимальными абелевыми идеалами лиева кольца $NT(n, K)$. Исследуем идеалы
  $H^((m))$ и $H^((n-m))$ для фиксированного $m >= n - m$. По
  лемме~@lem:l1983-characteristic-centralizers
  $
    C(Gamma_(n-m)) = N_(m+1,n-m) subset H^((i)) subset C(Gamma_m),
    quad i = m, n - m.
  $ <eq:l1983-abelian-centralizer-bounds>
  При $n = 2 m$ получаем $H^((m)) = N_(m+1,m)$. Поэтому далее $n - m < m < n$.

  #source(6, printed: 68)Обозначим через $H_(p q)^((i))$ совокупность элементов
  матриц из $H^((i))$ на месте $(p, q)$. Включения
  $H^((i)) supset H^((i)) ast K epsilon_(p q)$, $p > q$, в частности,
  $
    H^((i)) supset K epsilon_(r s) ast (H^((i)) ast K epsilon_(p q))
    = K H_(s p)^((i)) K epsilon_(r q) quad (r > s > p > q),
  $ <eq:l1983-double-lie-inclusion>
  $
    H^((i)) supset K^2 H_21^((i)) epsilon_(s 1) quad (s >= 4),
    quad H^((i)) supset H_(n,n-1)^((i)) K^2 epsilon_(n t)
    quad (t <= n - 3),
  $ <eq:l1983-border-inclusions>
  показывают, что $H_(n-m+1,n-m)^((i)) epsilon_(m 1) subset H^((i))$. Используя
  абелевость идеала $H^((i))$ и @eq:l1983-elementary-product, получаем равенство
  $
    H^((i)) ast (H^((i)) inter K epsilon_(m 1))
    = H^((i))(H^((i)) inter K epsilon_(m 1)) = 0,
  $
  и, следовательно,
  $
    H_(m+1,m)^((i)) H_(n-m+1,n-m)^((i)) = 0, quad i = m, n - m.
  $
  В силу леммы~@lem:l1983-characteristic-centralizers
  $C(Gamma_m) = C(Gamma_(m-1)) + H^((m)) + H^((n-m))$ и, следовательно,
  $H_(i+1,i)^((m)) + H_(i+1,i)^((n-m)) = K$. По
  лемме~@lem:l1983-peirce-decomposition кольцо $K$ содержит идемпотент $e_m$
  такой, что
  $
    H_(m+1,m)^((i)) = K e_i,
    quad H_(n-m+1,n-m)^((i)) = e_(n-i) K, quad i = m, n - m,
  $ <eq:l1983-peirce-coordinate-images>
  где $e_(n-m) = 1 - e_m$. Пользуясь абелевостью $H^((i))$ ($i = m, n - m$),
  находим
  $
    H^((i)) inter K epsilon_(m 1) = e_(n-i) K epsilon_(m 1),
    quad H^((i)) inter K epsilon_(n,n-m+1) = K e_i epsilon_(n,n-m+1).
  $ <eq:l1983-border-intersections>
  Если $m > n - m + 1$, то в силу @eq:l1983-double-lie-inclusion,
  @eq:l1983-border-inclusions, $K e_m K epsilon_(i+1,i) subset H^((n-i))$,
  $i = m, n - m$, и, следовательно, $e_m K = K e_m K = K e_m$, т. е. $e_m$ —
  центральный идемпотент по лемме~@lem:l1983-peirce-decomposition. При
  $n - m < m < n - 1$ произведение $H^((m+1)) ast H^((n-m))$ по модулю $Gamma_3$
  равно нулю, и поэтому, в силу @eq:l1983-abelian-centralizer-bounds,
  @eq:l1983-peirce-coordinate-images,
  $e_m lr((1 - e_(m+1))) = e_(m+1)(1 - e_m) = 0$, т. е. $e_m = e_(m+1)$. Тем
  самым доказано существование идемпотента $e$ в центре кольца $K$, для которого
  $H_(i+1,i)^((i)) = e K$, $H_(n-i+1,n-i)^((i)) = (1 - e)K$ при всех $i$,
  $1 <= i < n$, $n != 2 i$.

  Соотношения @eq:l1983-abelian-centralizer-bounds,
  @eq:l1983-peirce-coordinate-images, @eq:l1983-border-intersections доказывают
  первое утверждение леммы при $2 i - n = plus.minus 1$; случай $n = 2 i$
  доказан выше.

  Пусть $i = m$ или $n - m$, $m > n - m + 1$. Из
  @eq:l1983-peirce-coordinate-images и @eq:l1983-double-lie-inclusion следует,
  что $H^((i)) supset e_i K epsilon_(n v)$, $v < m$. Поэтому в силу абелевости
  идеала $H^((i))$ элементы его матриц в строках с номерами $v < m$ содержатся в
  правом аннуляторе множества $K e_i$, т. е. в $(1 - e_i)K$. Аналогично в
  столбцах с номерами $u > n - m + 1$ элементы матриц из $H^((i))$ содержатся в
  $K e_i$. В частности, $H_(u v)^((i)) = 0$, $n - m < v < u <= m$, так как
  $K e_i inter K(1 - e_i) = 0$.

  Допустим, что $m < n - 1$. Так как $H^((i)) H^((i)) subset N_(n 1)$ по лемме
  @lem:l1976-abelian-annihilator [@bib:l1983-Levchuk1976Article], то для
  произвольных матриц $lr(‖a_(k t)‖)$ и $lr(‖b_(k t)‖)$ из $H^((i))$ должны
  иметь
  $
    a_(m+1,n-m+1)(b_(n-m+1,t)(1 - e_i)) + (a_(m+1,m)e_i)b_(m t) = 0,
    quad 1 <= t <= n - m.
  $
  Оба слагаемых в левой части равенства должны равняться нулю, поскольку
  $(1 - e_i)K inter e_i K = 0$. Поэтому множества $H_(m t)^((i))$,
  $1 <= t <= n - m$, также содержатся в правом аннуляторе множества
  $K e_i = H_(m+1,m)^((i))$, т. е. в $(1 - e_i)K$. Аналогично
  $H_(u,n-m+1)^((i)) subset K e_i$, $m < u <= n$. Следовательно, $H^((i))$ при
  $n - m + 1 < m < n - 1$ содержится в абелевом идеале
  $e_i N_(m+1,m) + (1 - e_i)N_(n-m+1,n-m)$ и в силу максимальной абелевости
  совпадает с ним.

  Выясним строение идеала $H^((i))$, $i = 1$ или $n - 1$. По доказанному,
  $
    (1 - e_i)N_41 + e_i N_(n,n-3) subset.eq H^((i)) subset.eq
    N_(n-2,1) + N_(n 3) + (1 - e_i)N_21 + e_i N_(n,n-1).
  $
  При $alpha = lr(‖a_(k t)‖)$, $beta = lr(‖b_(k t)‖) in H^((i))$ имеем
  $(alpha ast K epsilon_32) ast beta = 0$ и, следовательно,
  $a_(n 3)b_21 + b_(n 3)a_21 = 0$. В силу @eq:l1983-peirce-coordinate-images
  можно считать, что $b_21 = 1 - e_i$. Поэтому существует элемент
  $a_i in K(1 - e_i)$ такой, что
  $
    a_(n 3)(1 - e_i) = a_i a_21 quad (lr(‖a_(k t)‖) in H^((i))),
    quad a_i lr((x y + y x)) = 0 quad (x, y in K).
  $
  Аналогично существует элемент $c_i in K e_i$, для которого
  $a_(n-2,1)e_i = a_(n,n-1)c_i$ ($lr(‖a_(k t)‖) in H^((i))$), причем
  $((K ast K) union {2})c_i = 0$. Далее. Произвольные #source(
    7,
    printed: 69,
  )матрицы $alpha, beta in H^((i))$, с точностью до прибавления к ним матриц из
  $H^((i)) ast epsilon_32 + H^((i)) ast epsilon_(n-1,n-2)$, удовлетворяют
  условиям:
  $
    a_31(1 - e_i) = a_(n,n-2)e_i = b_31(1 - e_i) = b_(n,n-2)e_i = 0.
  $
  Из условия $alpha ast beta = 0$ в этом случае получаем
  $
    (a_(n,n-1)b_(n-1,1) - b_(n,n-1)a_(n-1,1))
    + (a_(n 2)b_21 - b_(n 2)a_21) = 0.
  $
  Выражения в первой и второй скобках содержатся соответственно в $K(1 - e_i)$ и
  $K e_i$ и поэтому равны нулю. Отсюда и из @eq:l1983-peirce-coordinate-images
  вытекает существование элементов $b_i$, $d_i$ таких, что
  $
    a_(n 2)(1 - e_i) = b_i a_21,
    quad e_i a_(n-1,1) = a_(n,n-1)d_i quad (lr(‖a_(k t)‖) in H^((i))),
    b_i lr((K ast K))(1 - e_i) = (K ast K)d_i e_i = 0.
  $
  Таким образом, $H^((i))$ содержится в абелевом идеале
  $
    (epsilon_21 + a_i epsilon_(n 3) + b_i epsilon_(n 2))K(1 - e_i)
    + K e_i lr((epsilon_(n,n-1) + c_i epsilon_(n-2,1) + d_i epsilon_(n-1,1)))
    +
    (epsilon_31 + a_i epsilon_(n 2))K(1 - e_i)
    + K e_i lr((epsilon_(n,n-2) + c_i epsilon_(n-1,1)))
    + (1 - e_i)N_41 + e_i N_(n,n-3)
  $
  и в силу максимальной абелевости совпадает с ним. Это завершает доказательство
  леммы.
]

#lemma[
  Пусть $phi in Gc_n lr((K))$ (или $phi in Lambda_n lr((K))$), $n >= 3$, и
  существует центральный идемпотент $e$ кольца $K$ такой, что
  $(K epsilon_(i+1,i))^phi = e K epsilon_(i+1,i)
  + (1 - e)K epsilon_(n-i+1,n-i)$ ($mod Gamma_2$), $1 <= i < n$. Тогда
  существуют диагональный автоморфизм $delta$ и идемпотентно-кольцевой
  автоморфизм $tau$ присоединенной группы (соответственно ассоциированного
  кольца Ли), для которых автоморфизм $phi delta tau$ действует тождественно по
  модулю $Gamma_2$.
] <lem:l1983-normalize-first-layer>

#proof[
  По условию леммы равенства
  $
    (a epsilon_(i+1,i))^phi = a^(phi_i) epsilon_(i+1,i)
    + a^(phi'_i) epsilon_(n-i+1,n-i) quad (mod Gamma_2),
    quad a in K\, 1 <= i < n,
  $
  определяют гомоморфизмы $phi_i$ и $phi'_i$ аддитивной группы кольца $K$
  соответственно на $e K$ и $(1 - e)K$. Положим $a_i = 1^(phi_i)$,
  $a'_i = 1^(phi'_i)$ и докажем обратимость в кольце $K$ элементов вида
  $a_i + a'_j$. Лиево умножение в кольце $NT(n, K)$ совпадает по модулю
  $Gamma_3$ с коммутированием в присоединенной группе. Поэтому
  $
    N_(i+1,i-1)^phi = N_(i+1,i)^phi ast N_(i,i-1)^phi
    = e K epsilon_(i+1,i-1) + (1 - e)K epsilon_(n-i+2,n-i) =
    epsilon_(i+1,i)^phi ast N_(i,i-1)^phi
    = N_(i+1,i)^phi ast epsilon_(i,i-1)^phi quad (mod Gamma_3),
    quad 1 < i < n.
  $
  Учитывая, что $e K inter (1 - e)K = 0$, получаем равенства
  $e K = e K a_(i-1) = a_i e K$ и, следовательно, существуют элементы $b_(i-1)$,
  $c_i in e K$, для которых $e = b_(i-1)a_(i-1) = a_i c_i$, $1 < i < n$. При
  этом $b_j a_j c_j = c_j$, $1 < j < n - 1$. Положим $b_(n-1) = c_(n-1)$ и
  покажем, что равенства $e = a_j b_j = b_j a_j$ справедливы также и при
  $j = 1$, $n - 1$. Рассмотрим случай, когда $j = 1$ (случай $j = n - 1$
  доказывается аналогично). В силу выбора $phi$ при любом $x in e K$ существует
  $y in K$, для которого $(y epsilon_32)^phi = x epsilon_32$ ($mod Gamma_2$) и,
  следовательно, $(y epsilon_31)^phi = x a_1 epsilon_31$ ($mod Gamma_3$); когда
  $x a_1 = 0$, должны иметь $x = 0$. Поэтому из равенств
  $e K a_1 = e K = e K b_1 a_1$ следует, что $e K = e K b_1$. В частности,
  $e = x_1 b_1$ для некоторого элемента $x_1 in e K$. Для него имеем
  $x_1 = x_1 b_1 a_1 = a_1$. Таким образом, $e = a_1 b_1 = b_1 a_1$. Аналогично
  существуют элементы $b'_i in (1 - e)K$ такие, что
  $a'_i b'_i = b'_i a'_i = 1 - e$, $1 <= i < n$. Равенства
  $(a_i + a'_j)(b_i + b'_j) = (b_i + b'_j)(a_i + a'_j)
  = a_i b_i + a'_j b'_j = e + (1 - e) = 1$ доказывают обратимость в $K$
  элементов $a_i + a'_j$. Сейчас легко видеть, что автоморфизм $phi$, с
  точностью до умножения на диагональный автоморфизм (сопряжение
  $alpha arrow.r t alpha t^(-1)$, где $t = sum_(i=1)^n d_i epsilon_(i i)$,
  $d_1 = 1$, $d_(i+1) = d_i lr((b_i + b'_(n-i)))$, #source(
    8,
    printed: 70,
  )$1 <= i < n$), удовлетворяет дополнительному условию
  $
    epsilon_(i+1,i)^phi = e epsilon_(i+1,i)
    + (1 - e)epsilon_(n-i+1,n-i) quad (mod Gamma_2),
    quad 1 <= i < n.
  $
  Пользуясь инвариантностью относительно $phi$ соотношений
  @eq:l1983-elementary-lie-product по модулю $Gamma_3$, находим
  $(a b)^(phi_i) = a^(phi_i) b^(phi_(i-1))$, $1 < i < n$, $a, b in K$. Отсюда
  $phi_1 = phi_2 = dots = phi_(n-1)$, причем $phi_1$ — эндоморфизм кольца $K$
  (см. также [@bib:l1983-Levchuk1975,
  замечание~@rem:l1975-automorphisms-pavlov-weir]). Аналогично
  $phi'_1 = phi'_2 = dots = phi'_(n-1)$ и $phi'_1$ — антиэндоморфизм кольца $K$.
  Если $a^(phi_1) + a^(phi'_1) = 0$, то в силу характеристичности $Gamma_2$ и
  равенства $e K inter (1 - e)K = 0$ получим $a = 0$. Следовательно,
  $phi_1 + phi'_1$ — автоморфизм группы $K^+$. Допустим, что он переводит в $e$
  элемент $f$. Нетрудно убедиться, что $f$ — центральный идемпотент кольца $K$,
  а соответствующий ему автоморфизм присоединенной группы (или ассоциированного
  кольца Ли, в соответствии с выбором $phi$ в лемме) по модулю $Gamma_2$
  действует так же, как и $phi$. Это доказывает лемму.
]

#lemma[
  Если $phi$ — автоморфизм присоединенной группы кольца $NT(n, K)$, $n >= 5$,
  действующий тождественно по модулю $Gamma_2$, то элементы $a$, $c$ из
  леммы~@lem:l1983-images-maximal-abelian удовлетворяют условию
  $
    a(x^2 - x)(y^2 - y) = 0,
    quad (x^2 - x)(y^2 - y)c = 0, quad x, y in K.
  $
] <lem:l1983-extremal-parameters>

#proof[
  В силу выбора $phi$ и леммы~@lem:l1983-images-maximal-abelian
  $
    (x epsilon_21)^phi = x epsilon_21 + a x epsilon_(n 3)
    quad (mod N_31 + N_(n 2))
  $
  для элемента $a in K$ с условиями $2 a = 0$, $a(K ast K) = 0$. Кроме того,
  $phi$ оставляет на месте подгруппы $N_(i+1,i)$, $1 < i < n - 1$. В частности,
  $
    (x epsilon_32)^phi - x epsilon_32 = lr(‖x^(lambda_(i j))‖)
    in N_31 + N_42.
  $
  Матрицы
  $
    alpha = sum_(i=4)^n 1^(lambda_(i 2)) epsilon_(i 3)
    - 1^(lambda_31) epsilon_21
  $
  и $-alpha$ взаимно обратимы в присоединенной группе, причем
  $(-alpha) compose epsilon_32^phi compose alpha
  = epsilon_32^phi + epsilon_32^phi ast alpha = epsilon_32$ ($mod N_41$).
  Следовательно, с точностью до умножения $phi$ на внутренний автоморфизм
  (условия для $phi$ в лемме при таком умножении не изменяются), можно считать
  выполненным условие $epsilon_32^phi = epsilon_32$ ($mod N_41$). Пользуясь
  инвариантностью @eq:l1983-elementary-commutator относительно $phi$, получаем
  равенства
  $
    (z x epsilon_42)^phi = z x epsilon_42 + z x^(lambda_31) epsilon_41
    quad (mod N_52), quad z, x in K,
  $
  откуда $x^(lambda_31) = x 1^(lambda_31) = 0$, т. е. $beta_x in N_42$ и
  $(x epsilon_32)^phi = x epsilon_32 compose beta_x$. Стандартные коммутаторные
  соотношения сейчас дают
  $
    (x y epsilon_31)^phi = [x epsilon_32,
      y epsilon_21 compose a y epsilon_(n 3)] compose [beta_x, y epsilon_21] =
    x y epsilon_31 + a x y epsilon_(n 2) + a y x y epsilon_(n 1)
    + [beta_x, y epsilon_21], quad x, y in K.
  $
  Поэтому элемент $(x y)^lambda$ матрицы $(x y epsilon_31)^phi$ на месте
  $(n, 1)$ равен $x^(lambda_(n 2))y + a y^2 x$. Отсюда $y^lambda = a y^2$,
  $x^(lambda_(n 2)) = x^lambda - a x = a(x^2 - x)$,
  $(x y)^lambda = a y^2 x + a(x^2 - x)y$, так что $a(x^2 - x)(y^2 - y) = 0$,
  $x, y in K$. Аналогично убеждаемся, что и элемент $c$ удовлетворяет требуемому
  в лемме условию. Лемма доказана.
]

#lemma[
  Пусть $phi in Gc_n lr((K)) union Lambda_n lr((K))$, $n >= 4$, причем $phi$
  оставляет на месте множества $N_(i+1,i)$ по модулю $Gamma_(n-2)$
  ($1 <= i < n$), а по модулю $Gamma_2$ действует тождественно. Тогда
  $
    N_21^phi = (epsilon_21 + b epsilon_(n 2))K + N_31,
  $
  $
    N_(n,n-1)^phi = K(epsilon_(n,n-1) + d epsilon_(n-1,1)) + N_(n,n-2)
  $
  #source(9, printed: 71)для некоторых элементов $b, d in K$ с условием
  $b(K ast K) = (K ast K)d = 0$. Если при этом $phi in Gc_n lr((K))$, то кольцо
  $K$ допускает преобразования $lambda$ и $mu$ такие, что
  $(x + y)^lambda = x^lambda + y^lambda + b x y$,
  $(x + y)^mu = x^mu + y^mu + x y d$, $x, y in K$.
] <lem:l1983-central-parameter-functions>

#proof[
  Первое утверждение леммы вытекает при $n >= 5$ из
  леммы~@lem:l1983-images-maximal-abelian; несложно доказывается оно и при
  $n = 4$. Допустим далее, что $phi$ — автоморфизм присоединенной группы.
  Элемент матрицы $(x epsilon_21)^phi$ на месте $(n, 1)$ обозначим через
  $x^lambda$ ($x in K$). Из инвариантности соотношений
  @eq:l1983-elementary-addition относительно $phi$ получим
  $(x + y)^lambda = x^lambda + y^lambda + b x y$ ($x, y in K$). Аналогично
  существует преобразование $mu$ кольца $K$.
]

#lemma[
  Пусть $phi in Gc_n lr((K)) union Lambda_n lr((K))$, причем
  $N_(i j)^phi = N_(i j)$, $i > j$. Тогда $phi$ — автоморфизм кольца $NT(n, K)$.
] <lem:l1983-preserved-rectangles>

#proof[
  Указанный автоморфизм в силу его выбора и лемм~@lem:l1983-additive-extension,
  @lem:l1983-adjoint-extension аддитивен на множествах $N_(i j)$, а его
  ограничение $phi_0$ на элементарных матрицах сохраняет все соотношения
  @eq:l1983-elementary-lie-product–@eq:l1983-elementary-addition. Далее,
  нетрудно убедиться, что $phi$ является аддитивным продолжением $phi_0$ на
  кольцо $NT(n, K)$ и, кроме того, сохраняет присоединенное умножение. Остается
  заметить, что автоморфизм и аддитивной, и присоединенной групп кольца является
  автоморфизмом этого кольца.
]

В леммах~@lem:l1983-central-ring-automorphisms, @lem:l1983-inner-reduction через
$cal(S)$ обозначается подгруппа автоморфизмов кольца $NT(n, K)$, действующих
тождественно по модулю $Gamma_2$.

#lemma[
  Всякий автоморфизм из $cal(S)$, действующий тождественно по модулю
  $Gamma_(n-1)$ ($n >= 3$) на элементах $epsilon_(i+1,i)$,
  $i = 1, 2, dots, n - 1$, является центральным.
] <lem:l1983-central-ring-automorphisms>

#proof[
  При $n = 3$ имеем $cal(S) = Zc$ и поэтому можно считать, что $n > 3$. Выберем
  произвольный автоморфизм $theta in cal(S)$ такой, что
  $epsilon_(m+1,m)^theta = epsilon_(m+1,m)$ ($mod Gamma_(n-1)$) для всех $m$.
  Так как $theta in cal(S)$, то должны иметь
  $beta_i lr((x)) = (x epsilon_(i+1,i))^theta - x epsilon_(i+1,i)
  in Gamma_2 inter N_(i+1,i)$. Умножение матриц из $NT(n, K)$ на
  $epsilon_(m+1,m)^theta$ равносильно умножению на $epsilon_(m+1,m)$
  ($1 <= m < n$), так как $Gamma_(n-1)$ — аннулятор кольца $NT(n, K)$. Поэтому
  при $m != i + 1$, $x in K$ из @eq:l1983-elementary-product получаем равенства
  $epsilon_(m+1,m) beta_i lr((x))
  = epsilon_(m+1,m)^theta (x epsilon_(i+1,i))^theta = 0$, показывающие, что
  строки матрицы $beta_i lr((x))$ с номерами, отличными от $n$, $i + 1$,
  являются нулевыми. Аналогично из равенств
  $beta_i lr((x)) epsilon_(m+1,m) = 0$, $i != m + 1$, вытекает, что столбцы
  матрицы $beta_i lr((x))$ с номерами, отличными от $i$, 1, нулевые. При $i = 1$
  или $n - 1$ это доказывает равенства
  $(x epsilon_(i+1,i))^theta = x epsilon_(i+1,i)$ ($mod Gamma_(n-1)$), $x in K$.
  Справедливость этих равенств при $1 < i < n - 1$ сейчас получаем, пользуясь
  инвариантностью соотношений
  $(x epsilon_(i+1,i))(y epsilon_(i,i-1)) = x y epsilon_(i+1,i-1)$ и замечая,
  что, по доказанному, существуют $lambda_i, mu_i in End(K^+)$, для которых
  $(x epsilon_(i+1,i))^theta = x epsilon_(i+1,i)
  + x^(lambda_i) epsilon_(i+1,1) + x^(mu_i) epsilon_(n i)$
  ($mod Gamma_(n-1)$), $x in K$. Лемма доказана.
]

Индукцией по $k$ просто доказывается

#lemma[
  Для любого $k$, $1 < k < n$, всякий автоморфизм из $cal(S)$, с точностью до
  умножения на внутренний автоморфизм, действует тождественно на элементах
  $epsilon_(i+1,i)$ ($i = 1, 2, dots, n - 1$) по модулю $Gamma_k$.
] <lem:l1983-inner-reduction>

Из лемм~@lem:l1983-images-maximal-abelian,
@lem:l1983-extremal-parameters–@lem:l1983-inner-reduction вытекает

#lemma[
  Подгруппа автоморфизмов присоединенной группы кольца $NT(n, K)$ (автоморфизмов
  ассоциированного кольца Ли), действующих тождественно по модулю $Gamma_2$, при
  $n > 4$ совпадает с произведением $Zc Jc Uc^((c)) V$ (соответственно
  $Zc Jc Uc^ast V^ast$). При $n = 4$ она совпадает с произведением
  $Zc Jc Uc^((c))$ (соответственно $Zc Jc Uc^ast$).
] <lem:l1983-first-layer-kernel>

Исследуем произвольный автоморфизм $phi$ присоединенной группы кольца
$NT(4, K)$. Равенства
$
  (a epsilon_(i'+1,i'))^phi = a^(phi_(i 1)) epsilon_21
  + a^(phi_(i 2)) epsilon_43 quad (mod N_32),
  quad i = 1, 2 quad (1' = 1\, 2' = 3),
$
$
  (a epsilon_32)^phi = a^theta epsilon_32
  + a^(lambda_1) epsilon_31 + a^(lambda_2) epsilon_42
  quad (mod Gamma_3), quad a in K
$
сопоставляют ему в силу @eq:l1983-elementary-addition и характеристичности
подгрупп $N_32$ и $Gamma_3$ #source(10, printed: 72)эндоморфизмы $phi_(i j)$,
$lambda_i$ и автоморфизм $theta$ группы $K^+$. При этом
$
  [a epsilon_32, b epsilon_(i'+1,i')]^phi
  = [(a epsilon_32)^phi, (b epsilon_(i'+1,i'))^phi] =
  a^theta b^(phi_(i 1)) epsilon_31 - b^(phi_(i 2))a^theta epsilon_42 +
  (a^(lambda_2)b^(phi_(i 1)) - b^(phi_(i 2))a^(lambda_1)
    - b^(phi_(i 2))a^theta b^(phi_(i 1)))epsilon_41, quad a, b in K.
$
В частности, $K = 1^theta(K^(phi_11) + K^(phi_21))
= (K^(phi_12) + K^(phi_22))1^theta$ и, следовательно, $1^theta$ — обратимый
элемент. С точностью до умножения $phi$ на треугольный автоморфизм можно
считать, что $1^theta = 1$, $1^(lambda_1) = 1^(lambda_2) = 0$. В силу
@eq:l1983-elementary-commutator коммутатор $[a epsilon_32, b epsilon_21]$
(аналогично $[a epsilon_32, b epsilon_43]$) не будет изменяться при изменении
элементов $a$, $b$, если произведение $a b$ (соответственно $b a$) остается
неизменным. Полагая $c_(i j) = 1^(phi_(i j))$, из предыдущего равенства и
соотношения
$
  [(K epsilon_(i+2,i))^phi, (K epsilon_(i'+1,i'))^phi] = 0
$
получаем
$
  x^(phi_(i 1)) = x^theta c_(i 1),
  quad x^(phi_(i 2)) = c_(i 2)x^theta,
  quad i = 1, 2\, x in K;
  c_(i 2)(x^2 - x)^theta y^2 c_(i 1)
  = x^(lambda_2)y c_(i 1) - c_(i 2)y x^(lambda_1),
  quad i = 1, 2 quad (x, y in K);
$ <eq:l1983-rank-four-parameter-relations>
$
  (x y)^theta c_11 = x^theta y^theta c_11,
  quad c_12(x y)^theta = c_12 y^theta x^theta,
  1^theta = 1, quad (x y)^theta c_21 = y^theta x^theta c_21,
  quad c_22(x y)^theta = c_22 x^theta y^theta quad (x, y in K);
$ <eq:l1983-rank-four-multiplicativity>
$
  2 c_(i 2) K c_(i 1) = 0, quad i = 1, 2.
$ <eq:l1983-rank-four-two-annihilation>

Соотношения $epsilon_(i'+1,i')^(phi^(-1)) = g_(i 1) epsilon_21
+ g_(i 2) epsilon_43$ ($mod N_32$) определяют элементы $g_(i j)^theta = d_(i j)$
в кольце $K$, причем
$
  d_(i 1)c_11 + d_(i 2)c_21 = delta_(i 1),
  quad c_12 d_(i 1) + c_22 d_(i 2) = delta_(i 2),
  quad i = 1, 2,
$ <eq:l1983-rank-four-inverse-coordinates>
где $delta_(i j)$ — символ Кронекера. Подставляя в
@eq:l1983-rank-four-parameter-relations вместо $y$ элемент $d_(i 1)$, а затем
суммируя по $i$, получаем, используя
@eq:l1983-rank-four-multiplicativity–@eq:l1983-rank-four-inverse-coordinates:
$x^(lambda_2) = c_12 d_11(x^2 - x)^theta$. Аналогично находим
$x^(lambda_1) = (x^2 - x)^theta d_22 c_21$. С учетом
@eq:l1983-rank-four-multiplicativity равенство
@eq:l1983-rank-four-parameter-relations сейчас принимает вид
$
  c_(i 2)(x^2 - x)y(d_(1 i) + d_(2 i))c_(i 1)
  = c_(i 2)(x^2 - x)y^2 c_(i 1),
  quad i = 1, 2 quad (x, y in K).
$ <eq:l1983-rank-four-quadratic-condition>

Далее, соотношения
@eq:l1983-rank-four-multiplicativity–@eq:l1983-rank-four-quadratic-condition
показывают, что отображение
$
  a epsilon_(i'+1,i') arrow.r a^theta c_(i 1) epsilon_21
  + c_(i 2)a^theta epsilon_43,
  quad i = 1, 2 quad (1' = 1\, 2' = 3),
  a epsilon_32 arrow.r a^theta epsilon_32
  + (a^2 - a)^theta d_22 c_21 epsilon_31
  + c_12 d_11(a^2 - a)^theta epsilon_42,
$ <eq:l1983-rank-four-adjoint-map>
сохраняет соотношения @eq:l1983-elementary-commutator,
@eq:l1983-elementary-addition и поэтому определяет эндоморфизм $eta$
присоединенной группы. По лемме~@lem:l1983-adjoint-extension он является
автоморфизмом, так как
$
  (a epsilon_41)^eta = (c_22 a^theta c_11 + c_12 a^theta c_21)epsilon_41
  = (a epsilon_41)^phi.
$
Учитывая, что $N_21^(phi eta^(-1))$ — абелев идеал лиева кольца $NT(4, K)$
[@bib:l1983-Levchuk1976Article, теорема @th:l1976-normal-lie-correspondence],
находим $(epsilon_43 ast N_21^(phi eta^(-1))) ast N_21^(phi eta^(-1)) = 0$,
откуда $N_21^phi subset N_21 + N_43$. Аналогично $N_43^phi subset N_21 + N_43$.
Поэтому $phi$ и $eta$ действуют одинаково по модулю $Gamma_2$. Тем самым
доказана

#lemma[
  Всякий автоморфизм присоединенной группы кольца $NT(4, K)$ является
  произведением автоморфизма, действующего тождественно по модулю $Gamma_2$, на
  диагональный автоморфизм и на автоморфизм @eq:l1983-rank-four-adjoint-map,
  определяемый для элементов $c_(i j)$, $d_(i j) in K$ и автоморфизма $theta$
  группы $K^+$ с условиями
  @eq:l1983-rank-four-multiplicativity–@eq:l1983-rank-four-quadratic-condition.
] <lem:l1983-rank-four-adjoint-decomposition>

Аналогично доказывается

#lemma[
  Всякий автоморфизм лиева кольца $NT(4, K)$ является произведением
  автоморфизма, действующего тождественно по модулю $Gamma_2$, #source(
    11,
    printed: 73,
  )на диагональный автоморфизм и на автоморфизм, определяемый по закону
  $
    a epsilon_21 arrow.r a^theta c_11 epsilon_21 + c_12 a^theta epsilon_43,
    quad a epsilon_32 arrow.r a^theta epsilon_32,
    a epsilon_43 arrow.r a^theta c_21 epsilon_21 + c_22 a^theta epsilon_43
    quad (a in K),
  $ <eq:l1983-rank-four-lie-map>
  где автоморфизм $theta$ группы $K^+$ и элементы $c_(i j)$ таковы, что система
  уравнений @eq:l1983-rank-four-inverse-coordinates разрешима в $K$ относительно
  $d_(i j)$, и выполнены условия @eq:l1983-rank-four-multiplicativity,
  @eq:l1983-rank-four-two-annihilation.
] <lem:l1983-rank-four-lie-decomposition>

#proof(head: [*Доказательство теоремы~@th:l1983-main-automorphisms.*])[
  Автоморфизмы кольца $NT(n, K)$ по лемме~@lem:l1983-characteristic-centralizers
  оставляют на месте множества $N_(i j)$ и, следовательно, удовлетворяют
  условиям леммы~@lem:l1983-normalize-first-layer для $e = 1$. Отсюда и из
  лемм~@lem:l1983-normalize-first-layer, @lem:l1983-central-ring-automorphisms,
  @lem:l1983-inner-reduction вытекает, что группа автоморфизмов кольца
  $NT(n, K)$ над ассоциативным кольцом $K$ с единицей разложима в произведение
  $Zc Tc AutK K$ подгрупп соответственно центральных, треугольных и кольцевых
  автоморфизмов. Очевидно, что автоморфизм аддитивной и присоединенной групп
  кольца $NT(n, K)$ является автоморфизмом этого кольца. Далее, указанные в
  теореме~@th:l1983-main-automorphisms разложения групп $Gc_n lr((K))$ и
  $Lambda_n lr((K))$, $n > 4$, вытекают из
  лемм~@lem:l1983-images-maximal-abelian, @lem:l1983-normalize-first-layer и
  @lem:l1983-first-layer-kernel. Нужно лишь заметить, что подгруппа диагональных
  автоморфизмов перестановочна с подгруппами $Phi$, $Phi^ast$ и, кроме того,
  $[Uc^ast, Jc] subset Jc$, $[V^ast, Jc] subset Zc Uc^ast$.

  Если аннулятор элемента 2 в кольце $K$ нулевой или если $K$ — некоммутативное
  кольцо без делителей нуля, то подгруппы $V^ast$ и $V$ тривиальны. Поэтому для
  доказательства теоремы~@th:l1983-main-automorphisms при $n = 4$ достаточно
  показать, что в обоих случаях автоморфизм
  $phi in Gc_4 lr((K)) union Lambda_4 lr((K))$ удовлетворяет условиям
  леммы~@lem:l1983-normalize-first-layer.

  В первом случае условие @eq:l1983-rank-four-two-annihilation дает
  $(c_(i 2)K)(K c_(i 1)) = 0$, $i = 1, 2$. Так как
  $K c_11 + K c_21 = c_12 K + c_22 K = K$, то по
  лемме~@lem:l1983-peirce-decomposition существует идемпотент $e$ такой, что
  $K c_11 = e K$,
  $
    K c_21 = (1 - e)K, quad c_12 K = K(1 - e), quad c_22 K = K e.
  $
  Из равенств $e K = K e c_11 = c_22 e K c_11 = c_22 e K = K e$ и
  леммы~@lem:l1983-peirce-decomposition следует, что $e$ лежит в центре кольца
  $K$. Поэтому в силу лемм~@lem:l1983-rank-four-adjoint-decomposition,
  @lem:l1983-rank-four-lie-decomposition $phi$ удовлетворяет условиям
  леммы~@lem:l1983-normalize-first-layer. В случае, когда $K$ — некоммутативное
  кольцо без делителей нуля, матрица $lr(‖c_(i j)‖)$, определяемая автоморфизмом
  $phi$ по лемме~@lem:l1983-rank-four-adjoint-decomposition или
  @lem:l1983-rank-four-lie-decomposition, является мономиальной в силу
  @eq:l1983-rank-four-multiplicativity и, следовательно, $phi$ удовлетворяет
  условиям леммы~@lem:l1983-normalize-first-layer при $e = 1$ или 0.
  Теорема~@th:l1983-main-automorphisms доказана.
]
