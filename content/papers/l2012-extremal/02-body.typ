#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": ht, ker

=== Нормальное строение <sec:l2012-extremal-normal-structure>

#source(5, printed: 159) Исследуем нормальное строение определённых групп
$U = U G(K)$.

Пусть ${r}^+$ при $r in G$ есть совокупность $s in G^+$ с неотрицательными
коэффициентами в линейном выражении $s-r$ через базу $Pi$. Положим

$
  T(r) = 〈 X_s | s in {r}^+ 〉, quad Q(r) = 〈 X_s | s in {r}^+ without {r} 〉.
$

Если $H subset.eq T(r_1) T(r_2) dots T(r_m)$ и включение нарушается при любой
замене $T(r_i)$ на $Q(r_i)$, то назовём ${r_1, r_2, dots, r_m} = cal(L)(H)$
_множеством углов_ для $H$. Когда $s$-проекция любого элемента из $H$ равна
произведению $r$-проекции на фиксированный скаляр, отличный от 0, назовём $r, s$
_связанными_ в $H$, а при $p, r+p, s+p in G^+$ мы также называем их
$p$-связанными.

_Фреймом_ для $H subset.eq U$ назовём такое множество $cal(F)(H)$, что

$
  cal(F)(H) subset.eq product_(s in cal(L)(H)) X_s, quad cal(F)(H) = H mod
  product_(s in cal(L)(H)) Q(s).
$

Ясно, что элементы из $H$ дают фрейм $cal(F)(H)$, если в их канонических
разложениях отбросить все сомножители с $r in.not cal(L)(H)$. Линейные методы в
исследовании нормального строения $U$ позволяет применять представление $pi$
группы $U$ в $N G(K)$ (см. раздел @sec:l2012-extremal-preliminaries). Фреймы в
$N Phi(K)$ определяем, полагая $cal(F)(pi(H)) = pi(cal(F)(H))$.

#lemma[Пусть $H subset.eq U Phi(K)$, $pi(H)$ — подгруппа аддитивной или
  присоединённой групп кольца Ли $N Phi(K)$ и $p in Phi^+$. Тогда
  $pi(cal(F)([H, X_p]))$ есть $K$-подмодуль в $N Phi(K)$, совпадающий с
  $cal(F)(pi(H) ast K e_p)$.] <lem:l2012-extremal-commutator-frame>

Структурные константы $c_(r s)$ базиса Шевалле определяют лиевы произведения
$e_r ast e_s = c_(r s) e_(r+s)$. В силу коммутаторной формулы Шевалле
$[X_r, X_s] = x_(r+s) lr((c_(r s) K)) mod Q(r+s)$. Используя соотношения из
[@bib:l2012-extremal-Levchuk1990, § @sec:l1990-small-f4-automorphisms (I)] и
[@bib:l2012-extremal-Levchuk2009, теорема 2], приходим к следующей лемме.

#lemma[Пусть $U = U G(K)$ и $r, s, r+s in G^+$. Тогда
  $[X_r, X_s] = X_(r+s) mod Q(r+s)$ или $G = Phi$, $c_(r s) K = p(Phi)! K = 0$ и
  $[X_r, X_s] subset.eq Q(r+s)$.] <lem:l2012-extremal-root-commutator>

Можно показать, что $|cal(L)([H, X_s])| <= 3$. Если $cal(L)(H) = {r}$,
$s, r+s in G^+$ и $[H, X_s] != X_(r+s) mod Q(r+s)$, то либо $G = Phi$ и
применима лемма @lem:l2012-extremal-root-commutator, либо $G$ — группа
скрученного типа, $r$-проекция $H$ порождает 1-мерный $K_sigma$-модуль и $s$
первого типа. Для некоторых типов полное описание $H$ даёт следующая теорема из
[@bib:l2012-extremal-Levchuk2008, теорема @th:l2008-normal-classical].

#theorem[Подгруппа $H$ группы $U G(K)$ типа $B_n$, $C_n$ для $2K = K$ или типа
  $A_n$, $twisted(2, A_m)$ нормальна тогда и только тогда, когда для любого её
  угла $r$ и $p in Pi(G)$ с $r+p in G$ имеем либо
  $cal(F)([H, X_p]) Q(r+p) subset.eq H$, либо $G = B_n$ и в $[H, X_p]$ два угла
  $q$-связаны для некоторого $q in Pi(G)$, в $[H, X_q]$ два угла связаны и
  $cal(F)([H, X_p]) cal(F)([H, X_q]) Q(r+p, r+p+q) subset H$.]
<th:l2012-extremal-classical-normal>

#source(6, printed: 160) Более сложное нормальное строение имеют группы $U$ типа
$D_n$ и $twisted(2, D_n)$ [@bib:l2012-extremal-Levchuk2008,
@bib:l2012-extremal-Suleimanova2008, @bib:l2012-extremal-Suleimanova2008E]. Для
них существуют максимальные абелевы нормальные подгруппы $M$, такие что вес
коммутаторов $[dots [[M, U], U] dots, U]$, не порождаемых корневыми подгруппами,
неограничено растёт вместе с $n$ [@bib:l2012-extremal-Levchuk2008, теоремы
@th:l2008-normal-orthogonal и @th:l2008-normal-classical-maximal]. Однако
справедлива следующая теорема.

#theorem[Пусть $U$ есть группа типа $E_n$ или классического типа над полем $K$.
  Если $2K = K$, то подгруппа $H$ нормальна в $U$ тогда и только тогда, когда
  $cal(F)([H, X_p]) subset.eq H$ при любом $p in Pi$. Для типа $D_n$ (или
  $twisted(2, D_n)$) если $H lt.closed.eq U$ и
  $cal(F)([H, X_p]) subset.eq.not H$, то существуют простые углы
  $r, overline(r)$ (соответственно $zeta(r)$) и $p$-связанный угол в $H$ с
  проекциями $H$ порядка 2 на эти углы.] <th:l2012-extremal-frame-normal>

Для групп $U$ классического типа максимальные абелевы нормальные подгруппы
перечислены в [@bib:l2012-extremal-Levchuk2008, теорема
@th:l2008-normal-classical-maximal] с использованием описания в
[@bib:l2012-extremal-Levchuk1990] централизаторов $C(T(r))$ подгрупп $T(r)$. Для
группы $U A_n lr((K))$ (т. е. группы $U$ типа $A_n$), изоморфной унитреугольной
группе $UT(n+1, K)$, они были перечислены ранее в
[@bib:l2012-extremal-Levchuk1976, теорема @th:l1976-maximal-abelian] (случай
конечного поля $K$ нечётного порядка рассмотрен в [@bib:l2012-extremal-Weir1955,
теорема 7]).

#lemma[С точностью до сопряжения диагональным автоморфизмом всякая максимальная
  абелева нормальная подгруппа группы $U A_n lr((K))$ есть либо $T(p)$, либо

  $
    alpha(K) lr((C(T(r)) inter C(T(r')))), quad alpha(t) = x_r lr((t)) x_(r')
    lr((t)) quad (t in K), quad r+r' = rho,
  $ <eq:l2012-extremal-alpha-subgroup>

  либо при $2K = 0$, $n >= 3$ дополнительно

  $
    beta(K) lr((C(T(r)) inter C(T(r')))) {x_r lr((t)) x_(r') lr((t)) x_(r+p)
      lr((c t)) | t in K} quad (c in K), beta(t) = x_(r+p) lr((t)) x_(r'+p)
    lr((t)), quad r+r'+p = rho,
  $ <eq:l2012-extremal-beta-subgroup>

  для подходящих $r, r' in Phi^+$ и простого корня
  $p$.] <lem:l2012-extremal-an-maximal-abelian>

Подмножество $Psi$ в $Phi^+$ называем _нормальным_, если ${s}^+ subset.eq Psi$
для всех $s in Psi$ и, следовательно,
$X_Psi = 〈 X_r | r in Psi 〉 lt.closed.eq U Phi(K)$. Подмножество $Psi$ в
$Phi^+$ называем, следуя А. И. Мальцеву [@bib:l2012-extremal-Malcev1945],
_коммутативным_ или _абелевым_, если $r+s in.not Phi$ для всех $r, s in Psi$. В
этом случае $X_Psi$ есть прямое произведение корневых подгрупп. При
$H subset.eq U G(K)$ положим

$ Psi(H) = {r in G^+ | H inter X_r != 1}. $

Совокупность углов каждого элемента из $H$, не лежащих в $Psi(H)$, и сумм таких
углов в $G^+$ обозначаем через $hat(Psi)(H)$. Для подгрупп $H$ вида
@eq:l2012-extremal-alpha-subgroup или @eq:l2012-extremal-beta-subgroup выполнено
$hat(Psi)(H) = {r, r', rho}$ или $hat(Psi)(H) = {r, r', r+p, r'+p, rho}$
соответственно.

Нормальное замыкание $M_0$ в группе $U D_n lr((K))$ подгруппы $alpha(K)$ с
простыми углами $r$ и $r' = overline(r)$ абелево при $2K = 0$, и
$hat(Psi)(M_0) = {r}^+ union {r'}^+$. Когда $n = 4$, существуют такие
$p, q in Pi(Phi)$, что $M_0$ имеет вид

$
  alpha(K) beta(K) lr((C(T(r)) inter C(T(r')))) {x_(r+p+q) lr((t)) x_(r'+p+q)
    lr((t)) | t in K}.
$ <eq:l2012-extremal-d4-normal-closure>

#theorem[#source(7, printed: 161) Пусть $M$ — максимальная абелева нормальная
  подгруппа группы $U = U Phi(K)$, $p(Phi)! K = K$. Тогда $Psi = Psi(M)$ —
  абелево нормальное подмножество и $X_Psi subset.eq M$. При $M != X_Psi$ с
  точностью до сопряжения диагональным автоморфизмом либо
  $X_(hat(Psi)) tilde.eq UT(3, K)$ и $M$ имеет вид
  @eq:l2012-extremal-alpha-subgroup, либо $2K = 0$, $p(Phi) = 1$ и
  $X_(hat(Psi)) inter M$ имеет $p$-связанные углы для простого корня $p$, причём
  имеются следующие возможности:

  #enum(
    numbering: ru-enum,
    [$M$ имеет вид @eq:l2012-extremal-beta-subgroup и
      $X_p X_(hat(Psi)) tilde.eq UT(4, K)$,],
    [$U = U D_4 lr((2)) = X_(hat(Psi)) X_p$,],
    [$M$ имеет вид $M_0$ для типа $D_n$ или @eq:l2012-extremal-d4-normal-closure
      для типа $E_m$,],
    [$U$ типа $D_n$ или $E_m$ и $M$ вида

      $
        {x_(r_1) lr((t)) x_(r_2) lr((t)) x_(r_3) lr((t)) x_(r_2+p) lr((c t)) | t
          in K} {x_(r_1+p) lr((t)) x_(r_2+p) lr((t)) | t in K} times {x_(r_1+q)
          lr((t)) x_(r_3+q) lr((t)) | t in K} X_Psi
      $ <eq:l2012-extremal-three-angle-subgroup>

      для некоторых $s in Psi$, $r_1, r_2, r_3 in hat(Psi)$, простых $p, q != p$
      и $c in K$.
    ],
  )] <th:l2012-extremal-abelian-normal>

=== Максимальные абелевы нормальные подгруппы
<sec:l2012-extremal-exceptional-abelian>

Перечислим максимальные абелевы нормальные подгруппы групп $U$ исключительного
типа. Для случая лиева ранга, не превосходящего 2, доказана следующая теорема.

#theorem[В группе $U$ ранга, не превосходящего 2, все максимальные абелевы
  нормальные подгруппы исчерпываются следующими подгруппами:

  #enum(
    numbering: ru-enum,
    [$〈 gamma 〉 U_2$ ($gamma in U without U_2$) при $G = twisted(2, B_2)$;],
    [$U_2$ при $G = twisted(2, G_2)$ или $G = G_2$, $3K = 0$;],
    [$U_3$ при $G = G_2$, если $6K = K$, и, кроме того, $beta_c lr((K)) dot U_4$
      ($c in K$), если $2K = 0$, а при $|K| = 2$ также
      $〈 alpha 〉 times 〈 beta_1 lr((1)) 〉$, где

      $
        alpha = x_a lr((1)) x_(2a+b) lr((1)), quad beta_c lr((t)) = x_(a+b)
        lr((t)) x_(2a+b) lr((t c));
      $
    ],
    [$U_3$ при $G = twisted(3, D_4)$ и, если $2K = 0$, с точностью до сопряжения
      диагональным автоморфизмом подгруппы
      $beta_c lr((K_sigma)) x_(2a+b) lr((K^(1+sigma))) dot U_4$ ($c in K$), а
      при $|K_sigma| = 2$ также

      $
        〈 alpha 〉 times 〈 beta_1 lr((1)) 〉 times x_(2a+b) lr((K^(1+sigma))).
      $
    ],
  )] <th:l2012-extremal-rank-two-maximal>

По теореме @th:l2012-extremal-abelian-normal для групп $U$ типа $E_m$ нам
достаточно перечислить коммутативные нормальные подмножества систем корней $Phi$
типа $E_m$, включающие все максимальные (с точностью до симметрии для типа
$E_6$), и корни, характеризующие подгруппы
@eq:l2012-extremal-alpha-subgroup–@eq:l2012-extremal-three-angle-subgroup.
Соответственно выбору ранга $m = 6$, $m = 7$ или $m = 8$ число Кокстера равно
12, 18 или 30 (см. [@bib:l2012-extremal-Bourbaki1972, таблицы V—VII]; простые
корни $alpha_i$ ($1 <= i <= m$) и граф Кокстера см. в разделе
@sec:l2012-extremal-preliminaries). Положим

$
  a alpha_1 + b alpha_2 + c alpha_3 + d alpha_4 + e alpha_5 + dots + f alpha_m =
  lr((a c[d b]' e dots f)) = vec(delim: #none, a c d e dots f, b).
$

#heading(level: 4, numbering: none)[А. Коммутативные нормальные подмножества,
  включающие все максимальные] <ss:l2012-extremal-e-commutative-sets>

#source(8, printed: 162) Тип $E_6$:

$ {alpha_1}^+, quad {tilde(mu)_4}^+, $

где $tilde(mu)_4 = lr((01[21]'10))$ (максимальный корень подсистемы типа $D_4$ с
корнем $alpha_4$),

$
  {11[10]'11}^+ union {tilde(mu)_4+alpha_1}^+ union {tilde(mu)_4+alpha_6}^+,
  quad {11[10]'10}^+ union {01[21]'21}^+.
$

Тип $E_7$:

$
  {alpha_7}^+, quad {12[32]'210}^+ union {00[11]'111}^+, quad {12[21]'100}^+,
$

$
  {12[31]'210}^+ union {01[21]'111}^+, quad {01[21]'210}^+,
$

$ {11[21]'210}^+ union {01[21]'211}^+ quad "(немаксимальное)", $

$
  {12[21]'210}^+ union {12[21]'111}^+ union {01[21]'211}^+, quad {12[21]'110}^+
  union {01[21]'221}^+.
$

Тип $E_8$:

$
  {12[32]'2100}^+, quad {12[31]'3210}^+,
$

$ {12[32]'3210}^+ union {12[31]'3211}^+ quad "(немаксимальное)", $

$
  {12[32]'2210}^+ union {12[31]'3321}^+, quad {12[42]'3210}^+ union
  {12[31]'2221}^+,
$

$
  {13[42]'3210}^+ union {12[21]'2221}^+, quad {23[42]'3210}^+ union
  {11[21]'2221}^+,
$

$
  {12[32]'3210}^+ union {12[32]'2221}^+ union {12[31]'3221}^+, quad
  {01[21]'2221}^+.
$

#heading(level: 4, numbering: none)[Б. Корни $r$, определяющие подгруппы
  @eq:l2012-extremal-alpha-subgroup] <ss:l2012-extremal-e-alpha-roots>

Тип $E_6$:

$ lr((11[11]'00)), quad lr((11[11]'10)), quad tilde(mu)_4. $

Тип $E_7$:

$ lr((11[10]'111)), quad lr((12[21]'100)), quad lr((12[21]'110)), $

$ lr((11[21]'210)), quad lr((11[21]'111)), quad lr((11[11]'111)). $

Тип $E_8$:

$
  lr((12[32]'2111)), quad lr((12[32]'2211)), quad lr((12[31]'3211)), quad
  lr((12[32]'3211)),
$

$ lr((12[21]'2221)), quad lr((11[21]'2221)), quad lr((01[21]'2221)). $

#heading(level: 4, numbering: none)[В. Пары ${r,p}$ для типа $E_6$ и ${r,r'}$
  для типов $E_7$, $E_8$, определяющие подгруппы
  @eq:l2012-extremal-beta-subgroup] <ss:l2012-extremal-e-beta-pairs>

Тип $E_6$:

$
  {lr((11[11]'00)), alpha_5}, quad {lr((11[11]'10)), alpha_6}, quad
  {lr((11[11]'10)), alpha_4}.
$

Тип $E_7$:

$
  {lr((12[21]'110)), lr((11[21]'111))}, quad {lr((12[21]'100)),
    lr((11[21]'211))},
$

$
  {lr((12[21]'110)), lr((11[21]'210))}, quad {lr((11[21]'210)),
    lr((11[21]'111))},
$

$
  {lr((12[21]'210)), lr((11[11]'111))}, quad {lr((12[31]'210)),
    lr((11[10]'111))}.
$

#source(9, printed: 163) Тип $E_8$:

$
  {lr((12[31]'3221)), lr((12[32]'2111))}, quad {lr((12[31]'3211)),
    lr((12[32]'2211))},
$

$
  {lr((12[31]'2221)), lr((12[31]'3211))}, quad {lr((12[31]'2221)),
    lr((12[32]'2211))},
$

$
  {lr((12[21]'2221)), lr((12[32]'3211))}, quad {lr((11[21]'2221)),
    lr((12[42]'3211))}.
$

#heading(level: 4, numbering: none)[Г. Углы ${r,r'}$, определяющие подгруппу
  @eq:l2012-extremal-d4-normal-closure с $q$-связанными углами в коммутаторе
  $[M, X_p]$] <ss:l2012-extremal-e-d4-pairs>

$ {lr((11[10]'10)), lr((01[10]'11))}, $

$
  {lr((01[21]'210)), lr((01[21]'111))}, quad {lr((12[31]'3210)),
    lr((12[32]'2210))}
$

для типов $E_6$, $E_7$ и $E_8$ соответственно.

#heading(level: 4, numbering: none)[Д. Попарно $p$- или $q$-связанные углы
  ${r_1,r_2,r_3}$ подгрупп
  @eq:l2012-extremal-three-angle-subgroup] <ss:l2012-extremal-e-three-angles>

$ {lr((11[11]'10)), tilde(mu)_4, lr((01[11]'11))} $

для типа $E_6$,

$ {lr((12[21]'110)), lr((11[21]'210)), lr((11[21]'111))} $

для типа $E_7$,

$ {lr((12[31]'2221)), lr((12[31]'3211)), lr((12[32]'2211))} $

для типа $E_8$.

Оставшиеся группы $U$ типа $twisted(2, E_6)$, $F_4$, $twisted(2, F_4)$
ассоциируются с системой корней $Phi$ типа $F_4$ (см. раздел
@sec:l2012-extremal-preliminaries). Нам потребуется её представление из
[@bib:l2012-extremal-Levchuk1990,
@pass:l1990-small-f4-root-representation[представление корней]].

Согласно [@bib:l2012-extremal-Bourbaki1972, таблицы I—IV] и
[@bib:l2012-extremal-Levchuk1990] положительные корни систем типа $A_(n-1)$,
$B_n$, $C_n$, $B C_n$ или $D_n$ выражаются через ортонормированный базис
$epsilon_i$ ($1 <= i <= n$) евклидова пространства как

$
  epsilon_i - m epsilon_j = p_(i,m j), quad 1 <= j <= i <= n, quad m = 0, 1, -1.
$

В частности,

$ C_n^+ = {p_(i v) | 0 < |v| <= i <= n, v != i}. $

Для системы типа $B_n$ полагаем

$ epsilon_i - m epsilon_j = q_(i,m j), $

и поэтому

$ B_n^+ = {q_(i j) | 0 <= |j| < i <= n}. $

Как и в [@bib:l2012-extremal-Levchuk1990] (см.
@pass:l1990-small-f4-root-representation[диаграмму]), систему $F_4^+$
представляем как объединение $C_4^+ union B_4^+$ с заданным пересечением и явной
симметрией $overline(" ")$:

$
  B_4^+ inter C_4^+ = {p_(i,-i) = q_(i+1,i), q_(i,0) = p_(i+1,i) (i = 1, 3);
    p_(j,-j) = q_(j,1-j), q_(j,0) = p_(j,1-j) (j = 2, 4)};
$

$
  overline(p)_(i j) = q_(i j), quad overline(q)_(i j) = p_(i j) quad (1 <= |j| <
    i <= 4).
$

#source(10, printed: 164) В группах $U F_4 lr((K))$ и
$U twisted(2, E_6) lr((K))$ выделим следующие подгруппы, где $F = K$ и
$F = K_sigma$ соответственно:

$
  T(q_43) U_6, quad T(p_(4,-1)) T(q_(3,-2)), quad T(p_(4,-1)) {x_(q_(3,-2))
    lr((t)) x_(q_42) lr((t)) | t in F};
$ <eq:l2012-extremal-f4-odd-subgroups>

$
  T(p_42) X_(q_43), quad T(p_42) X_(p_43), quad T(p_(3,-2)), quad
  T(p_(3,-2))^tau, quad T(q_(3,-2)) X_(p_41) X_(p_(3,-2));
$ <eq:l2012-extremal-f4-even-root-subgroups>

$
  {x_(p_(3,-2)) lr((t)) x_(p_42) lr((t)) | t in K} S, quad S = T(q_43) T(p_41)
  "или" S = T(q_(3,-2)) X_(p_41);
$ <eq:l2012-extremal-f4-even-first-pairs>

$
  {x_(q_(3,-2)) lr((t)) x_(q_42) lr((t)) | t in K} T(p_(4,-1)) X_(p_41) S, quad
  S = X_(p_43) X_(p_42) "или" X_(p_(3,-2));
$ <eq:l2012-extremal-f4-even-second-pairs>

$
  〈 x_(p_43) lr((1)) x_(q_43) lr((d)) 〉 T(p_42) quad (d in K^*);
$ <eq:l2012-extremal-f4-cyclic-subgroups>

$
  [〈 x_(p_(3,-2)) lr((t)) x_(p_42) lr((t)) | t in K 〉 times 〈 x_(q_(3,-2))
    lr((t)) x_(q_42) lr((d t)) | t in K 〉] T(p_(4,-1)) X_(p_41).
$ <eq:l2012-extremal-f4-two-pair-subgroups>

Рассмотрим «корневые элементы» группы $U twisted(2, F_4) lr((K))$ (см. раздел
@sec:l2012-extremal-preliminaries). Пусть $r = q_(i j)$. Положим
$R_(i j) lr((t)) = x_r lr((t)) x_(overline(r)) lr((overline(t)))$, если
$(i,j) = (2,-1)$, $(3,2)$, $(3,-2)$ или $i = 4$, $j in {-3,-2,-1,1,2}$. При
$(i,j) = (2,1)$, $(3,1)$, $(3,-1)$, $(4,3)$ согласно
[@bib:l2012-extremal-Carter1972]
${r, overline(r), r+overline(r), r+2overline(r)}$ есть класс типа $B_2$. Положим
$R_(i j) lr((t)) = x_(overline(r)) lr((overline(t))) x_r lr((t))
x_(r+overline(r)) lr((t overline(t)))$
($t in K$). Согласно [@bib:l2012-extremal-Levchuk1990, §
@sec:l1990-small-twisted-f4 (I), @pass:l1990-small-twisted-f4-series[таблица
  центрального ряда]] подгруппу $U_i$ в $U twisted(2, F_4) lr((K))$ порождают
элементы $R_(i j) lr((t))$, соответствующие столбцам с номерами не меньше $i$ в
следующей таблице:

#table(
  columns: 8,
  align: center,
  stroke: none,
  $R_21$, $R_(2,-1)$, $R_(3,-1)$, $R_(3,-2)$, [], [], [], [],
  $R_32$, $R_31$, $R_43$, $R_42$, $R_41$, $R_(4,-1)$, $R_(4,-2)$, $R_(4,-3)$,
)

#theorem[Максимальные абелевы нормальные подгруппы в группах $U F_4 lr((K))$ и
  $U twisted(2, E_6) lr((K))$ с точностью до сопряжения диагональным
  автоморфизмом исчерпываются подгруппами @eq:l2012-extremal-f4-odd-subgroups
  при $2K = K$. Если $2K = 0$, то они исчерпываются подгруппами
  @eq:l2012-extremal-f4-even-root-subgroups–@eq:l2012-extremal-f4-two-pair-subgroups
  и соответственно @eq:l2012-extremal-f4-odd-subgroups,
  $lr((T(p_(3,-2)) inter E_6 lr((K_sigma)))) U_7$, а также

  $
    {x_(p_41) lr((t)) x_(p_(4,-1)) lr((f t)) | t in F} x_(p_(4,-1))
    lr((K_sigma)) T(q_43) U_7 quad (f in K without K_sigma).
  $ <eq:l2012-extremal-twisted-e6-even-subgroups>

  В группе $U twisted(2, F_4) lr((K))$ их исчерпывают подгруппы

  $
    〈 R_43 lr((1)) 〉 R_42 lr((K)) U_5, quad {R_(3,-2) lr((t)) R_42 lr((c t)) | t
      in K} U_5 quad (c in K).
  $ <eq:l2012-extremal-twisted-f4-maximal>
] <th:l2012-extremal-f4-e6-maximal>
