#import "../../main-defs.typ": *
#import "../../statements.typ": *

#lemma[
  Пусть $m = 2n$ или $2n-1$. Группа
  $N twisted(2, A_m) lr((K)) approx U twisted(2, A_m) lr((K))$
  порождается элементами $z epsilon_(i,-i)$ $(1 <= i <= n, z in Ker(1+sigma))$,
  $x epsilon_(i v)$ $(0 < abs(v) < i <= n, x in K)$ и еще, когда $m = 2n$,
  элементами $x epsilon_(i 0)$ $(x in K, 1 <= i <= n)$. Основными соотношениями
  между ними являются соотношения @eq:l1990-chevalley-root-addition при
  $v != 0$, @eq:l1990-chevalley-disjoint-commutator,
  @eq:l1990-chevalley-chain-commutator и следующие соотношения:

  #enum(
    numbering: ru-enum,
    [$[x epsilon_(j v), y epsilon_(i,-v)]
    = overline(x) y epsilon_(i,-j), quad i > j > abs(v) >= 0;$],
    [#source(10, printed: 323)$[x epsilon_(i j), y epsilon_(i,-j)]
      = (overline(x) y-x overline(y)) epsilon_(i,-i),
      quad i > j >= 0;$],
    [$[x epsilon_(i j), z epsilon_(j,-j)]
    = x z epsilon_(i,-j)-overline(x) x z epsilon_(i,-i),
    quad i > j > 0;$],
    [$[x epsilon_(i j), y epsilon_(j 0)]
    = x y epsilon_(i 0) compose (-x overline(tilde(y))) epsilon_(i,-j)
    compose (x overline(x) overline(tilde(y))-tilde(x y)) epsilon_(i,-i),
    quad i > j > 0;$],
    [$x epsilon_(i 0) compose y epsilon_(i 0)
    = (x+y) epsilon_(i 0)
    compose (tilde(x)+tilde(y)-tilde(x+y)+overline(x) y)
    epsilon_(i,-i), quad i > 0.$],
  )

  Здесь $tilde$ — преобразование кольца $K$ с условием:
  $tilde(x)+overline(tilde(x)) = x overline(x)$, $tilde(0) = 0$.
] <lem:l1990-chevalley-twisted-a-relations>

Заметим, что элементы из $N twisted(2, D_(n+1)) lr((K))$ и
$N twisted(2, A_(2n-1)) lr((K))$ можно представлять $B_n^+$-матрицами и
соответственно $C_n^+$-матрицами. Элемент группы $N twisted(2, A_(2n)) lr((K))$
естественно представлять $B C_n^+$-матрицей; она получается из $C_n^+$-матрицы
добавлением 0-го столбца.

Для группы $N G(K)$ $i$-е централ и гиперцентр по-прежнему обозначаем через
$Gamma_i$ и $Z_i$ соответственно; сохраняет смысл и обозначение $T(r)$ при
$r in G$ (см. введение). Обозначим также через $T_(i j)$ подгруппу группы
$N G(K)$ классического типа $G$, состоящую из элементов $lr(|a_(u v)|)$, где
$a_(u v) = 0$ при $u < i$ или $v > j$. При $r = rho_(i j)$ очевидно
$T(r) = T_(i j)$ за исключением случая $G = D_n$, $j = 1$. С помощью лемм
@lem:l1990-chevalley-classical-commutators–@lem:l1990-chevalley-twisted-a-relations
вычисляем централизатор $C(T_(i j))$.

#lemma[
  Положим $L = cal(Z)_2$ при $G = B_n$ или $C_n$,
  $L = Ann_(Ker(1+sigma)) K^(1-sigma)$ при $G = twisted(2, D_(n+1))$,
  $L = Ann_(Ker(1-sigma)) K^(1+sigma)$ при $G = twisted(2, A_m)$. Тогда в группе
  $N G(K)$ классического типа $G != A_n$ при $i < n$ имеем:
  $C(T_(i j)) = T_(1,-j-1)$ $(-n+1 < j < n)$, за исключением случая, когда
  $G = B_n$ или $twisted(2, D_(n+1))$, $j >= 0$, в котором
  $C(T_(i j)) = T_(1,-j-1)+sum_(k=j+1)^n L epsilon_(k 0)$. Равенства будут верны
  и для $i = n$, если в правых частях прибавить $T_(n,n-1)$ при $G = B_n$, $D_n$
  или $twisted(2, D_(n+1))$, $L dot T_(n,n-1)$ при $G = C_n$,
  $twisted(2, A_(2n-1))$ или $twisted(2, A_(2n))$.
] <lem:l1990-chevalley-classical-root-centralizers>

В леммах
@lem:l1990-chevalley-symplectic-central-series–@lem:l1990-chevalley-orthogonal-central-series
$L$ выбирается, как и в лемме @lem:l1990-chevalley-classical-root-centralizers.
Вместе с леммой @lem:l1990-chevalley-standard-central-series они дают описания
центральных рядов групп $N G(K)$ классических типов $G$. При $M subset G$
подгруппу группы $N G(K)$, порожденную множествами $K e_r inter N G(K)$ для
всевозможных $r in G without M$ высоты $>= i$, обозначаем через $L_i lr((M))$
или #source(11, printed: 324)$L_i lr(((k,l),(m,j),...))$, когда
$M = {rho_(k l),rho_(m j),...}$. Кроме того, $L_i = L_i lr((emptyset))$.

#lemma[
  Пусть $G = C_n$ или $twisted(2, A_(2n-1))$, $n >= 2$, и $(A,B)$ совпадает с
  $(K,2K)$ или соответственно, с $(Ker(1+sigma),K^(1-sigma))$. Тогда
  $
    Gamma_i = L_i lr(({(t,-t) | 1 <= t <= i} union {(i,-1)}))
    + sum_(i/2<t<i) B epsilon_(t,-t)
    + lr(⟨[K epsilon_(i 1), A epsilon_(1,-1)]⟩),
    quad 1 < i <= n;
  $
  $
    Gamma_i = L_i lr(({(t,-t) | 1 <= t <= n}))
    + sum_(i/2<t<=n) B epsilon_(t,-t), quad n < i < 2n;
  $
  $
    Z_i = L_(2n-i)+L dot L_(2n-i-1), quad 1 <= i < 2n-1,
    quad Z_(2n-1) = L_1.
  $
  Кроме того, $T_(i j)$, $i < n$, — характеристические подгруппы группы $N G(K)$
  при $n > 3$, а также при $Ann_L A = 0$, $n = 3$.
] <lem:l1990-chevalley-symplectic-central-series>

#proof[
  Члены $Gamma_i$, $Z_i$ находим (как и в леммах
  @lem:l1990-chevalley-even-unitary-central-series,
  @lem:l1990-chevalley-orthogonal-central-series) индукцией по $i$ с помощью
  лемм
  @lem:l1990-chevalley-classical-commutators–@lem:l1990-chevalley-classical-root-centralizers.
  Для большей наглядности их удобно представлять $Phi^+$-матрицами. Отметим, что
  подгруппа $lr(⟨[K epsilon_(i 1), A epsilon_(1,-1)]⟩)$ при $G = C_n$ совпадает
  с $K(epsilon_(i,-1)+epsilon_(i,-i))+cal(J)_2 epsilon_(i,-1)$. Далее
  устанавливаем характеристичность подгруппы $T_(1,m-1)+L dot T_(n m)$; она
  совпадает с $C(Gamma_(n+m))$ при $-n < m < 0$ и с
  $C(C(Gamma_(n-m))+Gamma_(n+m-1))$, когда либо $0 < m < n-2$, либо
  $Ann_L A = 0$, $m = n-2$. Следовательно, когда $n >= 4$ или $Ann_L A = 0$,
  $n = 3$, то подгруппы $T_(1,-1)$ и $T_(1,-1)^phi$ $(phi in Aut N G(K))$
  совпадают по модулю $Z_n$. Поскольку они являются максимальными абелевыми
  нормальными подгруппами, то
  $
    T_(2,-1) = [T_(1,-1)^phi,T_(2 1)]+C(Gamma_(n-1))
    subset T_(1,-1)^phi subset C(T_(2,-1)) = T_(1,-1),
    quad n >= 3,
  $
  откуда $T_(1,-1)^phi = T_(1,-1)$. Далее,
  $T_(2,-1) = T_(1,-1) inter (Gamma_2+Z_(2n-3)) = T_(2,-1)$ и
  $T_(2,-2)^phi = C(T_(2 1)^phi) subset C([T_(3 2),T_(2 1)^phi])
  subset C(T_(3 1)) = T_(2,-2)$, $n >= 4$, т.~е. подгруппы $T_(2,-2)$ и
  $T_(1 1) = C(T_(2,-2))$ характеристичны при $n > 3$. Они характеристичны и при
  $n = 3$. Нужно лишь заметить, что $T_(2,-2) = C(T_(2 1))$, а $T_(2 1)$
  однозначно характеризуется как максимальная нормальная подгруппа, содержащая
  $L_2 (= Gamma_2+Z_3)$, и абелева по #source(12, printed: 325)модулю
  $C(C(Gamma_4)) = T_(3,-2)+(Ann_A L) dot T_(2,-2)$. Учитывая изоморфизм
  $frac(N G(K), T_(1,-1)) approx UT(n, K)$ и теоремы
  @th:l1983-main-automorphisms, @th:l1983-rank-four из
  [@bib:l1990-chevalley-Levchuk1983], получаем характеристичность подгрупп
  $T_(1 j)$, $1 <= j <= n-2$, и их централизаторов $C(T_(1 j)) = T_(1,-j-1)$.
  Подгруппа $T_(i,i-1)$ $(1 < i < n)$ содержит характеристическую подгруппу
  $T_(i,-i)$ и по ее модулю есть максимальная абелева нормальная подгруппа; в
  частности, $T_(i,-i) supset [epsilon_(i+1,i),T_(i,i-1)^phi,T_(i,i-1)^phi]$, и
  поэтому $T_(i,i-1)^phi subset T_(1,i-1) inter T_(i,n-1) = T_(i,i-1)$. Отсюда
  вытекает последнее утверждение леммы.
]

#lemma[
  В группе $N twisted(2, A_(2n)) lr((K))$ выполняются равенства:
  $
    Gamma_i = L_i lr(({(t,-t) | i/2 <= t <= i}))
    + lr(⟨K^(1-sigma) epsilon_(t,-t) | i/2 <= t < i⟩),
    quad 1 < i <= 2n;
  $
  $
    Z_i = L_(2n+1-i)+L dot L_(2n-i) lr(((n-t,t-n)))
    +(L inter cal(Z)_2) epsilon_(n-t,t-n) quad "при" i = 2t;
  $
  $
    Z_i = L_(2n+1-i)+L dot L_(2n-i) quad "при нечетном" i,
    quad 1 <= i < 2n.
  $
  Ее подгруппы $T_(i j)$, $i < n$, при $L = 0$ являются характеристическими.
] <lem:l1990-chevalley-even-unitary-central-series>

#lemma[
  Пусть $G = B_n$ или $twisted(2, D_(n+1))$, а $(A,B)$ совпадает с $(K,2K)$ или
  с $(Ker(1-sigma),K^(1+sigma))$ соответственно. Тогда
  $
    Gamma_i = L_(i+1) lr(((i,-1)))+B dot L_i
    + sum_(j=1)^(n-i) A epsilon_(i+j,j)
    + lr(⟨[A epsilon_(i 1), K epsilon_(1 0)]⟩)
    quad (1 < i <= n),
  $
  $
    Gamma_i = L_(i+1)+B dot L_i, quad n < i < 2n;
  $
  $
    Z_(n-i) = L_(n+i)+L dot R_(n-lr([(n-i)/2]))+L' dot R_(i+1),
    quad 1 <= i < n,
  $
  $
    Z_(n+i) = L_(n-i)+L' dot R_1+L' dot R_(n-lr([(n-i)/2]))
    + sum_(j=1)^(i+1) L epsilon_(n-1-i+j,j),
    quad 0 <= i < n-1;
  $
  где $R_m = sum_(j=m)^n K epsilon_(j 0)$, $L' = {a in L | a^2 = 0}$. Если
  $L = 0$, $n >= 4$, то подгруппы $T_(i j)$, $i < n$, — характеристические.
] <lem:l1990-chevalley-orthogonal-central-series>

#proof[
  Отметим лишь, что при $L = 0$ подгруппы
  $
    #source(13, printed: 326)T_(2 0) = [C(Z_(n-2)),C(Z_(n-1))]+C(Z_n),
    quad n >= 4,
    quad T_(2,-1) = C(T_(2 0)), quad T_(1 0) = C(T_(2,-1))
  $
  характеристические. Подгруппа $T_(1 i)$, $1 <= i < n$, есть централизатор по
  модулю $T_(2,-1)$ подгруппы
  $(T_(2,-1)+T_(i+1,i)) inter T_(1 0) = T_(2,-1)+T_(i+1,0)$ и, следовательно,
  также характеристична. Далее продолжаем, как и в лемме
  @lem:l1990-chevalley-symplectic-central-series.
]

Рассматривая по аналогии с типом $twisted(2, D_m)$ тип $twisted(2, E_6)$,
получаем следующее утверждение.

#lemma[
  Ряд $L_1 supset L_2 supset dots$ является верхним центральным рядом в группах
  $N twisted(2, D_m) lr((K))$ $(m >= 4)$, $N twisted(2, E_6) lr((K))$
  (аналогично в группе $N twisted(2, A_m) lr((K))$) тогда и только тогда, когда
  $Ann_(Ker(1+sigma)) K^(1-sigma) = 0$ (соответственно
  $Ann_(Ker(1-sigma)) K^(1+sigma) = 0$). Нижним центральным рядом он является
  тогда и только тогда, когда $K^(1+sigma) = Ker(1-sigma)$ (соответственно
  $K^(1-sigma) = Ker(1+sigma)$).
] <lem:l1990-chevalley-twisted-central-series-criterion>

#lemma[
  Всякий автоморфизм $phi$ группы $N D_n lr((K))$, $n >= 5$, с точностью до
  умножения на идемпотентно-графовый автоморфизм, оставляет на месте подгруппы
  $T_(i j)$ при $i < n$.
] <lem:l1990-chevalley-orthogonal-characteristic-subgroups>

#proof[
  По лемме @lem:l1990-chevalley-standard-central-series, $Gamma_i = L_i$. С
  помощью леммы @lem:l1990-chevalley-classical-root-centralizers вычисляем
  централизаторы $C(Gamma_i)$. Соотношения
  $
    T_(3 1)^phi = [T_(3 2)^phi,T_(2 1)^phi]
    subset [C(Gamma_n),C(Gamma_(n-1))]
    subset [T_(2 2)+T_(n,n-1),T_(2 1)+T_(n 2)] = T_(3 1)
  $
  дают характеристичность подгрупп $T_(3 1)$, $T_(3,-2) = C(T_(3 1))$,
  $T_(2 1) = C(T_(3,-2))$, а также $T_(2 2)$, поскольку
  $[T_(3 2)^phi,T_(3 1)] subset T_(3,-2)$. Так как $phi$ индуцирует автоморфизм
  фактор-группы $frac(N D_n lr((K)), T_(2 1)) approx UT(n-1, K)$, то в силу
  теорем @th:l1983-main-automorphisms, @th:l1983-rank-four из
  [@bib:l1990-chevalley-Levchuk1983] подгруппы $T_(2 j)$,
  $T_(2,-j-1) = C(T_(2 j))$, $1 <= j < n$, характеристичны. Используя
  соотношения $[[epsilon_(n j),T_(j,j-1)^phi],T_(j,j-1)^phi] subset T_(2,-j)$,
  получаем характеристичность подгрупп $T_(j,j-1)$, $1 < j < n$. Фактор-группа
  $T_(2 3)/T_(4 3)$ изоморфна $UT(4, K)$. Следовательно, по теореме
  @th:l1983-rank-four из [@bib:l1990-chevalley-Levchuk1983] можно считать, что
  автоморфизм $phi$ с точностью до умножения на стандартный автоморфизм
  тождествен на $T_(3 2)+T_(4 3)$ по модулю $Gamma_2$ и на $epsilon_(3 2)$ по
  модулю $Gamma_3$, причем для некоторой матрицы $lr(|b_(u v)|) in SL(2, K)$
  имеем:
  $
    (y epsilon_(2 m'))^phi
    = y(b_(m 1) epsilon_(2,-1)+b_(m 2) epsilon_(2 1))
    mod Gamma_2, quad y in K,
  $
  $
    #source(14, printed: 327)0 = [epsilon_(4 3)^phi,
      [epsilon_(3 2)^phi,epsilon_(2 m')^phi],epsilon_(3 2)^phi]
    = b_(m 1) b_(m 2) epsilon_(4,-3),
    quad m = 1,2, quad 1' = -1, quad 2' = 1.
  $
  По лемме @lem:l1983-peirce-decomposition из [@bib:l1990-chevalley-Levchuk1983]
  существует идемпотент $e$ кольца $K$ такой, что $K b_(1 1) = K b_(2 2) = e K$,
  $K b_(1 2) = K b_(2 1) = (1-e)K$. Но тогда с точностью до умножения $phi$ на
  идемпотентно-графовый автоморфизм $e = 1$. Учитывая, что $T_(2,-1)$ —
  максимальная абелева нормальная подгруппа, получаем
  $
    T_(3,-1) subset [T_(3 2),T_(2,-1)^phi]+T_(3,-2)
    subset T_(2,-1)^phi subset C(T_(3,-1)) = T_(2,-1),
  $
  т.~е. $T_(2,-1)^phi = T_(2,-1)$. Из доказанного легко следует утверждение
  леммы.
]

Пусть $phi in Aut N G(K)$ и либо $G = D_n$, $n >= 5$, либо $G = C_n$ или
$twisted(2, A_(2n-1))$, $n >= 4$, либо $L = 0$, $G = twisted(2, A_(2n))$, $B_n$
или $twisted(2, D_(n+1))$, $n >= 4$. В силу лемм
@lem:l1990-chevalley-symplectic-central-series–@lem:l1990-chevalley-orthogonal-central-series,
@lem:l1990-chevalley-orthogonal-characteristic-subgroups, подгруппы
$T_(n,n-1)^phi = H$ и $T_(n,n-2)$ порождают всю группу и
$H = T_(n,n-1) mod T_(n,n-2)$. Замкнутость $H$ относительно коммутирования с
$epsilon_(n-1,n-2)$, $epsilon_(n-2,n-3)$, $T_(n-3,n-4)$ дает включение
$T_(n,n-4) subset H$. Но $T_(n,n-1)$ — нормальная подгруппа, максимальная
абелева по модулю $Gamma_m$, где $m = 2n-1$ при $G = C_n$ или
$twisted(2, A_(2n-1))$ и $m = 2n$ в остальных случаях. Следовательно, $H$ лежит
в централизаторе по модулю $Gamma_m$ подгруппы $T_(n,n-4)$, т.~е. в
$T_(n,n-1)+T_(1,-n+3)$. Учитывая включение
$Gamma_m supset [[[H,epsilon_(n-1,n-3)],epsilon_(n-2,n-3)],H]$, получаем
$
  T_(n,n-4) subset T_(n,n-1)^phi,
  quad T_(n,n-1)^phi = T_(n,n-1) mod T_(1,-n+3).
$ <eq:l1990-chevalley-classical-last-root-invariance>

=== #[ ] <sec:l1990-chevalley-symplectic-automorphisms>

#enum(
  numbering: ru-enum,
  [
    Рассмотрим автоморфизм $phi$ группы $N C_n lr((K))$, $n >= 4$. По лемме
    @lem:l1990-chevalley-symplectic-central-series $phi$ индуцирует автоморфизм
    фактор-группы $frac(N C_n lr((K)), T_(2,-2)) approx UT(n+1, K)$. В силу
    теоремы @th:l1983-main-automorphisms [@bib:l1990-chevalley-Levchuk1983], с
    точностью до умножения на стандартный автоморфизм, $phi$ тождествен по
    модулю $T_(2,-2)+T_(n,n-1)$. Пусть $lr(|x_(u v)^((i))|)$ — образ
    относительно $phi$ элемента $x epsilon_(i,i-1)$ при $1 < i <= n$ и элемента
    $x epsilon_(1,-1)$ при #source(15, printed: 328)$i = 1$, $x in K$. Умножив
    $phi$ на сопряжение элементом из $T_(2,-2)+L_(n-1)$, добьемся условий:
    $
      1_(i,-m)^((i)) = 0, quad 1 <= m < i <= n;
      quad 1_(n,-i)^((i)) = 0, quad 1 <= i < n.
    $ <eq:l1990-chevalley-symplectic-coordinate-normalization>

    Перестановочность элемента $lr(|x_(u v)^((i))|)$ с $epsilon_(j+1,j)^phi$,
    $1 <= i < j < n$, показывает, что ненулевыми у него могут быть лишь $i$-я и
    $n$-я строки, $1 <= i < n$. Элементы $y epsilon_(j+1,j)$ и
    $x epsilon_(m,m-1)$, $1 < m < j < n$, перестановочны и в то же время
    коммутатор их образов при $j <= n-2$ равен
    $
      [y x_(n,j)^((m)) epsilon_(n,-j-1)
        -y_(n,-m+1)^((j+1)) x epsilon_(n,-m)]
      -y_(j+1,-m)^((j+1)) x epsilon_(j+1,-m).
    $
    Когда $j = n-1 > m+1$, то выражение в квадратных скобках заменяется на
    $2y x_(n,-n+1)^((m)) epsilon_(n,-n)$, а при $(j,m) = (n-1,n-2)$ оно
    заменяется выражением
    $
      2y x_(n,-n+1)^((n-2)) epsilon_(n,-n)
      -2y_(n-2,-n+3)^((n)) x epsilon_(n-2,-n+2)
      -y_(n-1,-n+3)^((n)) x epsilon_(n-1,-n+2).
    $
    Поэтому у элемента $lr(|x_(u v)^((i))|)$ по модулю центра $1 <= i <= n$ либо
    $(-s)$-й столбец при $s >= 1$ нулевой, либо $i-2 <= s <= i$, либо
    $i = n > 3$, $s = n-3$.

    Рассмотрим коммутатор образов элементов $y epsilon_(i+1,i)$ и
    $x epsilon_(i,i-1)$, $1 < i <= n-2$, $x,y in K$. Он симметричен относительно
    $x$, $y$. Его $(i+1,m)$-координата при $-i < m < 0$ равна $y x_(i m)^((i))$
    и в силу @eq:l1990-chevalley-symplectic-coordinate-normalization равна нулю.
    Далее находим:
    $
      0 = [epsilon_(i+1,i-1)^phi,(K epsilon_(i,i-1))^phi]
      = K_(n,-i+1)^((i)) epsilon_(n,-i-1), quad 1 < i <= n-2;
    $
    $
      (y x epsilon_(i+1,i-1))^phi
      = y x epsilon_(i+1,i-1)
      +(y x_(i,-i)^((i))-y_(i+1,-i+1)^((i+1)) x) epsilon_(i+1,-i)
      -y_(n,-i+1)^((i+1)) x epsilon_(n,-i)
      #source(16, printed: 329)+(2y x y_(i+1,-i+1)^((i+1))-y^2 x_(i,-i)^((i)))
      epsilon_(i+1,-i-1)
      +(y x_(n,-i)^((i))+y x y_(n,-i+1)^((i+1))) epsilon_(n,-i-1);
    $
    $
      0 = [y epsilon_(i+1,i),x epsilon_(i+2,i-1)]^phi
      = y x_(i,-i)^((i)) epsilon_(i+2,-i-1)
      -y_(n,-i+1)^((i+1)) x epsilon_(n,-i-1),
      quad 1 < i <= n-3.
    $
    Поэтому на $K epsilon_(i,i-1)$, $2 <= i <= n-3$, $phi$ тождествен по модулю
    центра. Предыдущие равенства для $i = n-2$ также дают:
    $
      y_(n,-n+3)^((n-1)) = c y,
      quad x_(n,-n+2)^((n-2)) = c(x^2-x),
      quad 2c = c(x^2-x)(y^2-y) = 0, quad x,y in K.
    $
    Нужно лишь заметить, что координаты коммутатора
    $[y epsilon_(i+1,i),x epsilon_(i,i-1)]^phi$ есть функции от произведения
    $x y$. Рассматривая этот коммутатор для $i = n-1$, аналогично получаем:
    $
      (y x epsilon_(n,n-2))^phi = y x epsilon_(n,n-2)
      compose sum_(j=n-3)^(n-2)
      [(d_j x y^2+y x_(n-1,-j)^((n-1))) epsilon_(n,-j)
        -d_j x y epsilon_(n-1,-j)]
      compose (d_(n-2) y x^2-2x y_(n-1,-n+2)^((n)))
      epsilon_(n-1,-n+1)
      +A(x,y) epsilon_(n,-n+1)+B(x,y) epsilon_(n,-n);
    $ <eq:l1990-chevalley-symplectic-penultimate-image>
    $
      y_(n-2,-j)^((n)) = d_j y quad (d_j = 1_(n-2,-j)^((n))),
      quad x_(n-1,-j)^((n-1)) = d_j lr((x^2-x)),
      quad j = n-2,n-3, quad x,y in K.
    $
    Из перестановочности элементов $epsilon_(n-1,n-2)^phi$,
    $epsilon_(n,n-2)^phi$ сейчас получаем $d_(n-2) = 0$. Наконец,
    перестановочность образов элементов $x epsilon_(n-1,n-3)$,
    $t epsilon_(n,n-2)$ дает соотношения: $x_(n-2,-n+2)^((n-2)) = d_(n-3) x$,
    $d_(n-3) cal(J)_2 = 0$. С другой стороны, для любых элементов $c,d in K$ с
    условиями $d cal(J)_2 = 0$, $2c = 0$, $c cal(J)_2 cal(J)_2 = 0$ отображение
    $
      cases(
        y epsilon_(n,n-1) -> y(epsilon_(n,n-1)
          +d epsilon_(n-2,-n+3)),
        y epsilon_(n-1,n-2) -> y(epsilon_(n-1,n-2)
          +c epsilon_(n,-n+3)),
        t epsilon_(n-2,n-3) -> t epsilon_(n-2,n-3)
        +d t epsilon_(n-2,-n+2)+c(t^2-t) epsilon_(n,-n+2),
        #source(17, printed: 330)t epsilon_(n,n-2) -> t epsilon_(n,n-2)
        +d t(epsilon_(n-1,-n+3)+epsilon_(n,-n+3)),
        t epsilon_(n-1,n-3) -> t epsilon_(n-1,n-3)
        +d t(epsilon_(n-1,-n+2)+epsilon_(n-1,-n+1))
        +c t epsilon_(n,-n+2)+c t^2 epsilon_(n,-n+1),
        t epsilon_(n,n-3) -> t epsilon_(n,n-3)
        +d t(epsilon_(n-1,-n+2)+epsilon_(n,-n+1)+epsilon_(n,-n)),
        t in K,
        reverse: #true,
      )
    $ <eq:l1990-chevalley-symplectic-cd-automorphism>
    определяет автоморфизм группы $N C_n lr((K))$, $n >= 4$.
  ],
  [
    Умножением на автоморфизм вида
    @eq:l1990-chevalley-symplectic-cd-automorphism добиваемся тождественности
    $phi$ на $K epsilon_(n,n-1)$ по модулю $T_(n-1,-n+2)$, на
    $K epsilon_(n-1,n-2)$ по модулю $T_(n-1,-n+1)+T_(n,-n+2)$ и на
    $K epsilon_(i,i-1)$, $2 <= i <= n-2$, по модулю центра, $n >= 4$.
    Оказывается, к этому же случаю сводится исследование $phi$ и при $n = 3$.
    Действительно, поскольку $frac(N C_3 lr((K)), T_(2,-2)) approx UT(4, K)$,
    то, как показывают теорема @th:l1983-rank-four из
    [@bib:l1990-chevalley-Levchuk1983] и лемма
    @lem:l1990-chevalley-symplectic-central-series, достаточно установить
    включение $epsilon_(3 2)^phi in T_(3 2)+T_(2,-1)$. В силу тех же причин, с
    точностью до умножения $phi$ на диагональный, кольцевой и внутренний
    автоморфизмы, имеем $epsilon_(2 1)^phi = epsilon_(2 1) mod L_3$,
    $epsilon_(3 2)^phi = epsilon_(3 2)+t epsilon_(1,-1) mod T_(2,-1)$
    для некоторого $t in K$. Но тогда соотношение
    $0 = [epsilon_(3 2)^phi,epsilon_(2 1)^phi,epsilon_(2 1)^phi]
    = -t epsilon_(3,-2)-2t epsilon_(2,-1) mod T_(3,-3)$
    дает равенство $t = 0$.
  ],
  [
    Положим $1_(n-1,-n+2)^((n)) = b$, $n >= 3$, и для всех $y in K$
    $
      y^lambda = y_(n,-n+2)^((n)),
      quad y^mu = y_(n-1,-n+1)^((n-1)),
      quad y^(mu_j) = y_(n,-n+j)^((n-1)),
      quad j = 0,1,2.
    $
    Инвариантность относительно $phi$ соотношений
    @eq:l1990-chevalley-root-addition дает равенство
    $(y+z)^(mu_1) = y^(mu_1)+z^(mu_1)-z y^(mu_2)$. Обе его части симметричны по
    $y$, $z$, и поскольку $1^(mu_1) = 0$, то $y^(mu_2) = -2^(mu_1) y$. В силу
    симметричности $(n-1,-n+1)$-координаты в
    @eq:l1990-chevalley-symplectic-penultimate-image,
    $2y_(n-1,-n+2)^((n)) = 2b y$. Используя соотношение
    $
      0 = [t epsilon_(n,n-2),z epsilon_(n,n-1)]^phi
      = 3t z_(n-1,-n+2)^((n)) epsilon_(n,-n+1)
      +2[t z^lambda-b t(z^2+z)-z t^mu] epsilon_(n,-n),
    $
  ],
)
