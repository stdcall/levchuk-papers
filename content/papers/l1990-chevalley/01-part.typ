#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "diagrams/a-classical-matrices.typ": classical-matrices

#heading(level: 3, numbering: none)[Введение] <sec:l1990-chevalley-introduction>

#source(2, printed: 315)Унипотентную подгруппу группы Шевалле нормального или
скрученного типа $G$ над коммутативным кольцом $K$ с 1 (см.
[@bib:l1990-chevalley-Carter1972, § 5.1 и 13.6]) обозначаем через $U G(K)$. Её
автоморфизмы (наряду с коммутаторным строением) изучены, когда $K$ — поле
характеристики $!= 2,3$, в [@bib:l1990-chevalley-Gibbs1970] или когда $G = A_n$,
в [@bib:l1990-chevalley-Levchuk1975; @bib:l1990-chevalley-Levchuk1983]. В статье
автоморфизмы описаны (теоремы @th:l1990-chevalley-high-rank-automorphisms и
@th:l1990-chevalley-c-symplectic-automorphisms) при некоторых ограничениях на
кольцо $K$, зависящих от типа $G$, в частности, когда $K$ — произвольное поле;
выпадающие из рассмотрений группы $U G(K)$ малых рангов $G$ исследованы в
[@bib:l1990-chevalley-Levchuk1990, с. @ch:l1990-small].

Полученные результаты решают вопрос [@bib:l1990-chevalley-Kondratyev1986,
проблема 1.5] описания автоморфизмов, центральных рядов и характеристических
подгрупп группы $U G(K)$ над конечным полем $K$ характеристики 2 или 3.

Если автоморфизм группы единичен по модулю $m$-го гиперцентра, а по модулю
$m-1$-го гиперцентра при $m >= 1$ не является внутренним, его называют
гиперцентральным высоты $m$ или, кратко, гиперцентральным, когда группа не
совпадает с $m$-м гиперцентром. В исследованных в
[@bib:l1990-chevalley-Gibbs1970; @bib:l1990-chevalley-Levchuk1983] случаях
максимальная высота $ell = ell(G, K)$ гиперцентральных автоморфизмов группы
$U G(K)$ не превосходит 3. Когда $K$ — произвольное поле и $G != B_n,C_n$, или
когда $K$ — поле характеристики $!= 2$, $ell$ также ограничена функцией, не
зависящей от ранга $G$, в силу теорем
@th:l1990-chevalley-high-rank-automorphisms,
@th:l1990-chevalley-c-symplectic-automorphisms; более точно, $ell <= 5$. В общем
случае это не так. Например, для группы $U C_n lr((K))$ над совершенным полем
$K$ характеристики 2 и для группы $U B_n lr((K))$ над кольцом $K$ целых чисел
имеем $ell = n-1$.

Описание верхнего и нижнего центральных рядов группы $U G(K)$ над полем $K$,
полученное в [@bib:l1990-chevalley-Gibbs1970;
@bib:l1990-chevalley-Spitznagel1968; @bib:l1990-chevalley-Spitznagel1969] при
$char K != 2,3$, заключается в доказательстве их стандартности (см. также
[@bib:l1990-chevalley-Hurley1973]). Стандартный центральный ряд группы $U G(K)$
нормального типа $G = Phi$ образуют подгруппы $U_m$, порождаемые корневыми
подгруппами, соответствующими корням высоты $>= m$; при #source(
  3,
  printed: 316,
)$G = twisted(n, Phi_sigma)$ его образуют пересечения $U_m inter U G(K)$,
$m = 1,2,...$. Оказывается, что верхний и нижний центральные ряды скрученной
группы $U G(K)$ стандартны для всякого поля $K$; описание центральных рядов
групп $U G(K)$ классических типов $G$, а также всех нормальных типов $G = Phi$
удаётся получить для произвольного кольца $K$ (см. леммы
@lem:l1990-chevalley-standard-central-series,
@lem:l1990-chevalley-symplectic-central-series,
@lem:l1990-chevalley-even-unitary-central-series,
@lem:l1990-chevalley-orthogonal-central-series,
@lem:l1990-chevalley-twisted-central-series-criterion, а также
[@bib:l1990-chevalley-Levchuk1990, леммы @lem:l1990-small-g2-central-series,
@lem:l1990-small-twisted-central-series, @lem:l1990-small-f4-central-series]).

Результаты анонсировались в [@bib:l1990-chevalley-Levchuk1987a].

Если не оговорено противное, всюду ниже $K$ есть произвольное,
ассоциативно-коммутативное кольцо с 1; $cal(J)_m$ — его идеал, порождённый
множеством ${t^m-t | t in K}$, $cal(Z)_t$ — аннулятор элемента $t$ в кольце $K$
$(cal(Z)_t = Ann_K lr((t)))$. Подгруппа $T(r)$ группы $U Phi(K)$, $r in Phi$, по
определению, порождается корневыми подгруппами $X_s$, $s in Phi^+$, для которых
$s-r$ — линейная комбинация простых корней с неотрицательными коэффициентами
(определение имеет смысл и для скрученных групп).

=== #[ ] <sec:l1990-chevalley-hypercentral-automorphisms>

В системе корней $Phi$ существуют простой корень $q$ и корень $s$, для которых
$s+q$ — максимальный корень. Отображение
$
  x_q lr((t)) -> x_q lr((t)) x_s lr((d t)) x_(s+q) lr((t^lambda)),
  quad d = c_(s q) (2^lambda-2(1^lambda))
$ <eq:l1990-chevalley-extremal-automorphism>
(остальные корневые элементы остаются на месте) определяет автоморфизм группы
$U Phi(K)$ для любого преобразования $lambda$ кольца $K$ с условием
$(z+t)^lambda = z^lambda+t^lambda+c_(s q) d z t$ $(z,t in K)$; здесь $c_(s q)$ —
структурная константа алгебры Ли типа $Phi$ относительно базиса Шевалле. Ясно,
что при $2K = 0$ отображение @eq:l1990-chevalley-extremal-automorphism —
центральный (т.~е. действующий тождественно по модулю центра) автоморфизм. При
$cal(Z)_2 = 0$ вид $lambda$ указывает лемма @lem:l1983-quadratic-cocycle из
[@bib:l1990-chevalley-Levchuk1983]. Далее, если $Phi != C_n$, то
$c_(s q) = plus.minus 1$. При $Phi = C_n$ имеем $s-q in Phi$. Условие
продолжаемости до автоморфизма группы $U C_n lr((K))$, $n >= 2$, отображения
$
  x_q lr((t)) -> x_q lr((t)) x_(s-q) lr((b t)) x_s lr((t^(lambda_1)))
  x_(s+q) lr((t^lambda))
$ <eq:l1990-chevalley-cubic-c-automorphism>
с точностью до его умножения на внутренний автоморфизм равносильно требованиям
(знаки структурных констант выбраны, как в лемме
@lem:l1990-chevalley-classical-structure-signs):
$
  (z+t)^(lambda_1) = z^(lambda_1)+t^(lambda_1)-b t z,
  quad 1^(lambda_1) = 0,
  quad b = -2^(lambda_1),
  quad 2t^(lambda_1) = b(t-t^2),
$
$
  (z+t)^lambda = z^lambda+t^lambda+b t z(t+z-1),
  quad z,t in K.
$

#source(4, printed: 317)Последнее равенство в частных случаях при $t = z = 1$ и
$t = -z = 1$ при $3K = 0$ показывает, что $b = 0$; это очевидно при $2K = 0$.
Однако если $b = 0$, то $2K^(lambda_1) = 0$ и автоморфизм
@eq:l1990-chevalley-cubic-c-automorphism разложим в произведение внутреннего и
центрального автоморфизмов. С другой стороны, при $K = 2K = 3K$, полагая в
@eq:l1990-chevalley-cubic-c-automorphism $t^lambda = (b/3)t^3$,
$t^(lambda_1) = (-b/2)t^2$ $(t in K)$, как и в [@bib:l1990-chevalley-Gibbs1970,
с. 208], получаем автоморфизм для любого элемента $b in K$.

Выбор корней $q,s$ однозначен, за исключением случая $Phi = A_n$. Пусть
$Phi != C_n$ и ранг $Phi > 2$. Тогда существует простой корень $r$ с условиями:
$q+r$, $s-r in Phi^+$ и длины корней $q$, $r$, $q+r$, $s-r$, $s$, $s+q$
совпадают. Если $d in K$ и $2d = 0$, $d cal(J)_2 cal(J)_2 = 0$, то отображением
$
  cases(
    x_q lr((t)) -> x_q lr((t)) x_(s-r) lr((d t)),
    x_r lr((t)) -> x_r lr((t)) x_s lr((d(t^2-t))),
    x_(q+r) lr((t)) -> x_(q+r) lr((t)) x_s lr((d t))
    x_(s+q) lr((d t^2)),
    reverse: #true,
  )
$ <eq:l1990-chevalley-root-pair-hypercentral>
определяется автоморфизм группы $U Phi(K)$. В случаях $Phi = B_n$, $n >= 4$, и
$Phi = D_n$, $n >= 5$, имеется в точности две возможности выбора корня $r$,
скажем $r$ и $r'$. (При $Phi = D_4$ имеется три возможности выбора корня $r$, а
в оставшихся случаях корень $r$ определён однозначно.) При этом $q+r+r'$,
$s-r-r'$, $s-q-r'-r in Phi$ и отображением
$
  cases(
    x_(q+r'+r) lr((t)) -> x_(q+r'+r) lr((t)) x_(s-r) lr((c t))
    x_(s-r') lr((c t)) x_(s+q) lr((c t)),
    x_(q+a) lr((t)) -> x_(q+a) lr((t)) x_(s-r'-r) lr((c t))
    x_(s-r'-r+a) lr((c t)),
    x_a lr((t)) -> x_a lr((t)) x_(s-q-r'-r) lr((c t)),
    reverse: #true,
  ),
  quad a in {r,r'}
$ <eq:l1990-chevalley-double-root-hypercentral>
определяется автоморфизм группы $U Phi(K)$ для любого $c in Ann_K cal(J)_2$.
Если $rho$ — (единственный) короткий простой корень системы $Phi = B_3$ и
$b in K$, то при условии $3b = b(t^3-t) = 0$ $(t in K)$ отображением
$
  cases(
    x_q lr((t)) -> x_q lr((t)) x_(s-rho) lr((b t)),
    x_(2rho+q) lr((t)) -> x_(2rho+q) lr((t)) x_(s-rho) lr((-b t)),
    x_(q+rho) lr((t)) -> x_(rho+q) lr((t)) x_(q+r) lr((-b t))
    x_s lr((b t)),
    x_rho lr((t)) -> x_rho lr((t)) x_r lr((b t)),
    reverse: #true,
  )
$ <eq:l1990-chevalley-b3-hypercentral>
также определяется автоморфизм группы $U B_3 lr((K))$.

Простой корень $r$ с условиями $q+r,s-r in Phi^+$ существует (и единствен) и при
$Phi = C_n$, $n >= 3$, однако указанное ограничение на длины #source(
  5,
  printed: 318,
)корней здесь (как и для корня $rho$ при $Phi = B_3$) нарушается. При этом
$s-q-r$ — корень и любому элементу $b in K$ с условиями
$3b = 0 = b(t^3-t)(z^3-z)$ $(z,t in K)$ соответствует автоморфизм группы
$U C_n lr((K))$:
$
  cases(
    x_q lr((t)) -> x_q lr((t)) x_(s-r-q) lr((b t)) x_(s-r) lr((b t^2)),
    x_r lr((t)) -> x_r lr((t)) x_s lr((b(t^3-t))),
    x_(q+r) lr((t)) -> x_(q+r) lr((t)) x_(s-q) lr((b t))
    x_(s+q) lr((-b t^3)),
    reverse: #true,
  ).
$ <eq:l1990-chevalley-c-root-hypercentral>

Если $v$ — короткий корень максимальной высоты в системе корней $Phi = F_4$ или
$B_n$, $n >= 3$, и $cal(Z)_2 = 0$, то для всякого $c in K$ сопряжение элементом
$x_v lr((c/2))$ определяет автоморфизм группы $U Phi(K)$, называемый
полувнутренним; внутренним он является лишь при $c/2 in K$. Для проверки
автоморфности построенных отображений группы $U Phi(K)$ достаточно убедиться,
что они сохраняют основные соотношения — коммутаторную формулу Шевалле и
соотношения
$ x_r lr((t)) x_r lr((z)) = x_r lr((t+z)) quad (z,t in K, r in Phi^+). $

Если подгруппа $U twisted(n, Phi_sigma) lr((K))$ выдерживает автоморфизмы $phi$
и $phi^(-1)$ группы $U Phi(K)$, то ограничением $phi$ на подгруппе
$U twisted(n, Phi_sigma) lr((K))$ даётся её автоморфизм. Таким образом,
индуцируются, например, известные диагональные и кольцевые автоморфизмы группы
$U twisted(n, Phi_sigma) lr((K))$. Легко выделяются и произведения автоморфизмов
вида @eq:l1990-chevalley-extremal-automorphism группы $U A_m lr((K))$ (здесь
корень $q$ можно выбирать двумя способами: $q$ и $overline(q)$), которые
индуцируют автоморфизм группы $U twisted(2, A_m) lr((K))$.

#example[
  Пусть $ell_d$ — отображение множества корневых элементов группы
  $U A_m lr((K))$, заданное по формуле
  @eq:l1990-chevalley-root-pair-hypercentral, а отображение $ell'_d$ получено из
  $ell_d$ заменой $(q,s)$ на $(overline(q),overline(s))$ (см. также
  [@bib:l1990-chevalley-Levchuk1983, @pass:l1983-hypercentral-definitions[с.
    66]]). Если $K = GF(4)$, то отображением $ell_d dot ell'_(sigma(d))$
  определяется автоморфизм группы $U twisted(2, A_m) lr((K))$ для любого
  $d in K$; при $d != 0$ его нельзя продолжить до автоморфизма группы
  $U A_m lr((K))$ в силу теоремы @th:l1983-main-automorphisms из
  [@bib:l1990-chevalley-Levchuk1983], ср. [@bib:l1990-chevalley-Gibbs1970,
  следствие 7.2].
] <exm:l1990-chevalley-nonextendable-unitary>

Выделим подгруппу $V(G)$ автоморфизмов группы $U G(K)$. По определению, она
порождается автоморфизмами вида @eq:l1990-chevalley-extremal-automorphism,
@eq:l1990-chevalley-root-pair-hypercentral при $G = E_m$ $(m = 6,7,8)$, вида
@eq:l1990-chevalley-extremal-automorphism,
@eq:l1990-chevalley-root-pair-hypercentral или
@eq:l1990-chevalley-double-root-hypercentral при $G = D_n$ $(n >= 4)$, вида
@eq:l1990-chevalley-extremal-automorphism или
@eq:l1990-chevalley-c-root-hypercentral при $G = C_n$ $(n >= 3)$, вида
@eq:l1990-chevalley-extremal-automorphism, @eq:l1990-chevalley-b3-hypercentral
$(G = B_3)$ и полувнутренними автоморфизмами при $cal(Z)_2 = 0$, $G = B_n$
$(n >= 3)$, индуцированными автоморфизмами вида
@eq:l1990-chevalley-extremal-automorphism,
@eq:l1990-chevalley-root-pair-hypercentral или
@eq:l1990-chevalley-double-root-hypercentral при $G = twisted(2, E_6)$ или
$twisted(2, D_n)$ $(n >= 4)$, и, наконец, при $G = twisted(2, A_m)$ $(m >= 4)$ —
индуцированными автоморфизмами или их произведениями вида
@eq:l1990-chevalley-extremal-automorphism группы $U A_m lr((K))$, либо
автоморфизмами $ell_d ell'_(sigma(d))$ (см. пример
@exm:l1990-chevalley-nonextendable-unitary). К стандартным #source(
  6,
  printed: 319,
)автоморфизмам группы $U G(K)$ будем относить произведения её диагональных,
кольцевых (определения см., например, в [@bib:l1990-chevalley-Carter1972]),
внутренних, центральных и, кроме того, идемпотентно-графовых (они определены в
[@bib:l1990-chevalley-Levchuk1983; @bib:l1990-chevalley-Levchuk1990, §
@sec:l1990-small-standard-automorphisms] для $G = A_n$, $D_n$, $E_6$, $F_4$,
$B_2$, $G_2$) и графовых (при $G = D_4$) автоморфизмов. Ниже доказывается

#theorem[
  Всякий автоморфизм группы $U G(K)$ над коммутативным кольцом $K$ с 1,
  $G = D_m$ $(m >= 5)$, $E_m$ $(m = 6,7,8)$ есть произведение стандартного
  автоморфизма на автоморфизм из $V(G)$. Это верно и при $G = B_n$ или $C_n$
  $(n >= 3)$, если $cal(Z)_2 = 0$, при $G = twisted(2, A_m)$ $(m > 4)$, $D_4$,
  если $K$ — область целостности, при $G = twisted(2, E_6)$, $twisted(2, D_m)$
  $(m >= 4)$, если $K$ — поле.
] <th:l1990-chevalley-high-rank-automorphisms>

Отметим, что группа $U B_n lr((K))$ при $cal(Z)_2 = 0$, $2K != K$ имеет
полувнутренний автоморфизм, являющийся гиперцентральным автоморфизмом высоты
$n-1$. Если $K$ — совершенное кольцо характеристики 2, то
$U B_n lr((K)) approx.eq U C_n lr((K))$. (См. также автоморфизм
@eq:l1990-chevalley-symplectic-psi-map.) Автоморфизмы группы $U C_n lr((K))$
описаны в теореме @th:l1990-chevalley-c-symplectic-automorphisms.

=== #[ ] <sec:l1990-chevalley-classical-central-series>

Один из главных моментов в описании автоморфизмов группы $U G(K)$ заключается в
сведении изучения к гиперцентральным автоморфизмам. Здесь используется
характеристичность централов $Gamma_i$ и гиперцентров $Z_i$. Их описание для
типов $A_n$, $D_n$, $E_m$ включает

#lemma[
  Ряд $U_1 supset U_2 supset dots supset U_h = 1$ ($h$ — число Кокстера системы
  корней $Phi$) является нижним центральным рядом группы $U Phi(K)$ тогда и
  только тогда, когда $(rho(Phi)!)K = K$, где
  $rho(Phi) = max {lr((r,r))/lr((s,s)) | r,s in Phi}$. Он является также верхним
  центральным рядом, если аннулятор элемента $rho(Phi)!$ в кольце $K$ нулевой.
] <lem:l1990-chevalley-standard-central-series>

Доказательство получаем модификацией рассмотрений ряда в
[@bib:l1990-chevalley-Gibbs1970; @bib:l1990-chevalley-Spitznagel1968;
@bib:l1990-chevalley-Spitznagel1969].

При исследовании групп $U G(K)$ классических типов $G$ будем использовать такой
же подход, как и к группе $UT(n, K)$ в [@bib:l1990-chevalley-Levchuk1983].
Построим $K$-алгебру с базисом Шевалле $e_r$ $(r in Phi)$, ..., соответствующим
системе корней $Phi$ (см., например, [@bib:l1990-chevalley-Carter1972, § 4.4]),
и обозначим через $N Phi(K)$ подмодуль с базисом $e_r$ $(r in Phi^+)$. Всякий
элемент $A in U Phi(K)$ единственным способом представим как произведение
корневых элементов, в котором сомножители $x_r lr((t_r))$ $(r in Phi^+)$
расположены в соответствии с фиксированным (произвольно) упорядочением корней.
Положим $pi(A) = sum_(r in Phi^+) t_r e_r$.

Поскольку $pi$ — биективное отображение группы $U Phi(K)$ на $N Phi(K)$, то
равенства
$alpha compose beta = pi(pi^(-1)(alpha) pi^(-1)(beta))$
$(alpha,beta in N Phi(K))$ определяют групповую операцию на $N Phi(K)$.

Пусть $Phi$ — система корней типа $A_(n-1)$, $B_n$, $C_n$ или $D_n$ в евклидовом
#source(7, printed: 320)пространстве с ортонормированным базисом
$epsilon_1,epsilon_2,...,epsilon_n$. Систему положительных корней $Phi^+$ можно
составить из корней вида (см. [@bib:l1990-chevalley-Carter1972, таблицы I–IV]):
$
  epsilon_i-m epsilon_j = rho_(i,m j),
  quad 1 <= j < i <= n,
  quad m in {-1,+1}.
$
При $Phi = B_n$ сюда добавляются корни $epsilon_i = rho_(i,0)$, а при
$Phi = C_n$ — корни $2epsilon_i = rho_(i,-i)$, $1 <= i <= n$.

Полагая $e_r = epsilon_(i,m j)$ при $r = rho_(i,m j)$, произвольный элемент из
$N Phi(K)$ можно записать в виде $sum a_(i v) epsilon_(i v)$ и представить его
таблицей ($Phi^+$-матрицей) $||a_(i v)||$, в которой элемент $a_(i v)$, как
обычно, лежит в $i$-й строке и $j$-м столбце. $Phi^+$-матрица имеет вид:

#classical-matrices()

Отбрасывая в $B_n^+$-матрице нулевой столбец, получаем $D_n^+$-матрицу. Случаи,
когда сумма корней из $Phi^+$ есть корень, здесь, очевидно, исчерпываются
следующими: $rho_(i j)+rho_(j v) = rho_(i v)$,
$rho_(i v)+rho_(k,-v) = rho_(i,-k)$. Для корней $r,s in Phi^+$ имеем
$e_r ast e_s = C_(r s) e_(r+s)$, где $ast$ — умножение в лиевом кольце
$N Phi(K)$. Структурная константа Шевалле $C_(r s)$ определяется теоремой
Шевалле о базисе с точностью до умножения на $plus.minus 1$. С помощью
предложения 4.2.2 из [@bib:l1990-chevalley-Carter1972] и тождества Якоби
получается

#lemma[
  #source(8, printed: 321)Знаки структурных констант можно выбрать так, что
  $epsilon_(i j) ast epsilon_(j v) = epsilon_(i v)$ и выполняются равенства:
  $
    epsilon_(j v) ast epsilon_(i,-v) = epsilon_(i,-j)
    quad (Phi = B_n,D_n), quad i > j > |v| > 0;
  $
  $
    epsilon_(i 0) ast epsilon_(j 0) = 2epsilon_(i,-j)
    quad (Phi = B_n),
    quad epsilon_(i j) ast epsilon_(i,-j) = 2epsilon_(i,-i)
    quad (Phi = C_n), quad i > j >= 1;
  $
  $
    epsilon_(j m) ast epsilon_(i,-m)
    = epsilon_(i m) ast epsilon_(j,-m) = epsilon_(i,-j)
    quad (Phi = C_n), quad i > j > m >= 1.
  $
] <lem:l1990-chevalley-classical-structure-signs>

Базис Шевалле при $Phi = B_n,C_n,D_n$ далее будем выбирать так, как указано в
лемме @lem:l1990-chevalley-classical-structure-signs. Коммутатор элементов
$alpha,beta$ в группе $N Phi(K)$ обозначаем через $[alpha,beta]$. В частности,
$ x epsilon_(i v) compose y epsilon_(i v) = (x+y)epsilon_(i v), $
<eq:l1990-chevalley-root-addition>
$ [x epsilon_(i j), y epsilon_(k t)] = 0, quad j != k, i != t, t != -j, $
<eq:l1990-chevalley-disjoint-commutator>
$
  [x epsilon_(i j), y epsilon_(j v)] = x y epsilon_(i v),
  quad i > j > |v| > 0.
$ <eq:l1990-chevalley-chain-commutator>

#lemma[
  Коммутаторная формула Шевалле для группы $N Phi(K)$ при $Phi = B_n,D_n,C_n$
  равносильна соотношениям @eq:l1990-chevalley-disjoint-commutator,
  @eq:l1990-chevalley-chain-commutator и соотношениям:
  #enum(
    numbering: ru-enum,
    [$
      [x epsilon_(j v),y epsilon_(i,-v)] = cases(
        x y epsilon_(i,-j) quad i > j > |v| > 0,
        0 quad i = j > |v|
      ), quad Phi = B_n,D_n,
    $],
    [$
      [x epsilon_(i 0), y epsilon_(j 0)] = 2x y epsilon_(i,-j),
      quad [x epsilon_(i j), y epsilon_(j 0)]
      = x y epsilon_(i 0)+x y^2 epsilon_(i,-j),
      quad i > j > 0, quad Phi = B_n;
    $],
    [#source(9, printed: 322)$
        [x epsilon_(i j), y epsilon_(i,-j)] = 2x y epsilon_(i,-i),
        quad [x epsilon_(i j), y epsilon_(j,-j)]
        = x y epsilon_(i,-j)-x^2 y epsilon_(i,-i),
        quad i > j > 0;
      $],
    [$
      [x epsilon_(i k),y epsilon_(j,-k)]
      = [x epsilon_(j k),y epsilon_(i,-k)] = x y epsilon_(i,-j),
      quad i > j > k > 0, quad Phi = C_n.
    $],
  )
] <lem:l1990-chevalley-classical-commutators>

Пусть $K$ — кольцо с автоморфизмом $sigma$: $x -> overline(x)$ $(x in K)$,
второго порядка. Известно, что централизатор в группе $N D_(n+1) lr((K))$
автоморфизма
$
  x epsilon_(i v) -> -overline(x)epsilon_(i,-v)
  quad (1 = |v| < i <= n+1),
  quad x epsilon_(i v) -> overline(x)epsilon_(i v)
  quad (1 < |v| < i <= n+1)
$
изоморфен группе $U twisted(2, D_(n+1)) lr((K))$ и порождается элементами
$
  x epsilon_((i 0)) = x epsilon_(i+1,1)-overline(x)epsilon_(i+1,-1)
  quad (1 <= i <= n),
  quad z epsilon_((i,plus.minus j)) = z epsilon_(i+1,plus.minus (j+1))
  quad (1 <= j < i <= n),
$
$x,z in K$, $z = overline(z)$. Основные соотношения между ними вытекают из леммы
@lem:l1990-chevalley-classical-commutators. В записи элементов $epsilon_((i v))$
скобки иногда будем опускать. Отсюда

#lemma[
  Группа $U twisted(2, D_(n+1)) lr((K))$ изоморфна группе
  $N twisted(2, D_(n+1)) lr((K))$, порождаемой элементами $x epsilon_(i 0)$,
  $1 <= i <= n$, $x in K$; $z epsilon_(i v)$
  $(0 < |v| < i <= n, z in Ker(1-sigma))$, основные соотношения между которыми
  есть соотношения а) леммы @lem:l1990-chevalley-classical-commutators,
  @eq:l1990-chevalley-root-addition–@eq:l1990-chevalley-chain-commutator и
  соотношения:
  $
    [x epsilon_(i j),y epsilon_(j 0)]
    = x y epsilon_(i 0)+x y overline(y)epsilon_(i,-j),
  $
  $
    [x epsilon_(i 0),y epsilon_(j 0)]
    = (x overline(y)+overline(x)y)epsilon_(i,-j),
    quad i > j > 0.
  $
] <lem:l1990-chevalley-twisted-d-relations>

Рассматривая в группе $N A_m lr((K)) approx.eq UT(m+1, K)$ централизатор
автоморфизма $x e_r -> -overline(x)e_(overline(r))$, $x in K$, $r in Phi^+$ (см.
также [@bib:l1990-chevalley-Levchuk1987b, §
@sec:l1987-rings-automorphism-types]), аналогично получаем следующее
утверждение.
