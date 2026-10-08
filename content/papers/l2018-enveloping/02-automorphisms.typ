#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== #[ ] <sec:l2018-enveloping-automorphisms>

Основные операции кольца $R^((-))$ являются производными от операций в $R$.

#lemma[
  Автоморфизмы произвольного кольца $R$ образуют подгруппу в $Aut R^((-))$.
] <lem:l2018-enveloping-lie-automorphisms>

#source(3, printed: "рукопись 3")_Аннуляторные автоморфизмы_ колец выявляет (см.
[@bib:l2018-enveloping-Kuzucuoglu2001,
Lemma~@lem:l2001-automorphisms-annihilator])

#lemma[
  Пусть $zeta$ — аддитивное отображение произвольного кольца $R$ в аннулятор
  $Ann R={alpha in R | alpha R=R alpha=0}$. Отображение $1+zeta:x->x+zeta(x)$
  ($x in R$) есть эндоморфизм кольца $R$ тогда и только тогда, когда
  $zeta(R^2)=0$. Если $zeta(R^2)=0$ и $Ann R subset.eq R^2$, то
  $1+zeta in Aut R$.
] <lem:l2018-enveloping-annihilator-automorphisms>

Аннуляторные автоморфизмы кольца Ли — это, в точности, его _центральные
автоморфизмы_, то есть тождественные по модулю центра.

В [@bib:l2018-enveloping-Levchuk1990] использовалось обобщение. Когда кольцо Ли
(или группа) не совпадает с $m$-м гиперцентром, его автоморфизм называют
_гиперцентральным высоты $m$_ (или _гиперцентральным_), если по модулю $m$-го
гиперцентра он единичен, а по модулю $(m-1)$-го гиперцентра есть внешний
автоморфизм.

Считаем, по определению, что _степень_ $R^m$ неассоциативного кольца $R$
аддитивно порождают произведения конечной длины $>=m$ элементов из $R$.

Алгебра Ли $N Phi(K)$ над ассоциативно коммутативным кольцом $K$ с единицей
нильпотентна, как и его обертывающая алгебра $R$. Исследуем автоморфизмы кольца
$R$. Его порождают множества $K e_p$, $p in Pi$.

_Стандартный центральный ряд_ $L_1 supset.eq L_2 supset.eq dots supset.eq L_m
supset.eq dots$ в $N Phi(K)$ составляют идеалы $L_m$ с базой
${e_r | r in Phi^+, ht(r)>=m}$. Известно, что характеристичность $L_m$ в
$N Phi(K)$ может нарушаться, когда в кольце $K$ элемент $2$ или (тип $G_2$) $3$
необратим. С другой стороны, справедлива

#lemma[
  Идеалы $L_m$ в кольце $R$ характеристичны и $L_m=R^m$.
] <lem:l2018-enveloping-power-filtration>

Любой автоморфизм $theta$ кольца $K$, очевидно, индуцирует автоморфизм
$
  hat(theta): sum_(r in Phi^+) a_r e_r -> sum_(r in Phi^+) theta(a_r)e_r
$
кольца Ли $N Phi(K)$. Они образуют подгруппу $Ah(K) tilde.eq Aut K$ группы
$Aut R$.

Согласно [@bib:l2018-enveloping-Carter1972, §~7.1], каждому $K$-характеру $chi$
решетки корней (или аддитивной группы, порожденной корнями) в мультипликативную
группу $K^*$ обратимых элементов кольца $K$ соответствует _диагональный
автоморфизм_ $h(chi):e_r->chi(r)e_r$ ($r in Phi^+$) алгебры Ли $N Phi(K)$. В
группе $Aut N Phi(K)$ они образуют подгруппу $Dc$, изоморфную $|Pi|$-й прямой
степени группы $K^*$.

#source(4, printed: "рукопись 4")При ранге $Phi$ не меньше $2$ обозначим через
$Zc$ подгруппу центральных автоморфизмов кольца Ли $N Phi(K)$, порожденную
определенными ниже отображениями; она есть прямое произведение подгрупп
$zeta_r lr((End(K^+))) tilde.eq (End(K^+))^+$, $r in Pi$, где
$
  zeta_r lr((lambda)):x e_r |-> x e_r+lambda(x)e_rho,
  quad x e_s |-> x e_s quad (s in Phi^+, s!=r) quad (x in K)
$
для любого эндоморфизма $lambda$ аддитивной группы $K^+:=(K,+)$. Для типа $A_1$
полагаем $Zc=Aut(K^+)$, поскольку $R^2=0$.
#ed-note[В плохих характеристиках $Zc$ может не исчерпывать центральные
  автоморфизмы кольца Ли. Например, в типе $B_2$ над $GF(2)$ преобразование
  $e_beta |-> e_beta+e_(alpha+beta)$ при коротком $alpha$ и длинном $beta$
  центрально в кольце Ли, но не сохраняет умножение
  предложения~@prop:l2018-enveloping-multiplication.]
Ограничения корневых автоморфизмов $x_r lr((t))$ ($r in Phi^+$, $t in K$) на
алгебре Ли $N Phi(K)$ порождают подгруппу $Jc$ ее _внутренних автоморфизмов_.

Согласно [@bib:l2018-enveloping-Levchuk2016; лемма
@lem:l2016-hypercentral-symmetric-root-subgroup], для простых симметричных
корней $r$ и $overline(r)!=r$ ($overline(overline(r))=r$) системы $Phi$ типа
$D_n$ ($n>=4$) определено изоморфное вложение $∼$ подгруппы
$
  S={A=lr(||a_(u v)||) in SL(2, K):2a_(11)a_(12)=2a_(21)a_(22)=0}
$ <eq:l2018-enveloping-symmetric-root-subgroup>
группы $SL(2, K)$ в группу автоморфизмов алгебры Ли $N Phi(K)$ по правилу
$
  tilde(A):e_r->a_(11)e_r+a_(12)e_(overline(r)),
  quad e_(overline(r))->a_(21)e_r+a_(22)e_(overline(r)),
  quad e_s->e_s quad (s in Pi without {r,overline(r)}).
$

Известно [@bib:l2018-enveloping-Levchuk1983,
теорема~@th:l1983-main-automorphisms], что группа автоморфизмов кольца
$R=NT(n, K)$ (тип $A_(n-1)$), $n>=3$, допускает разложение (даже с
некоммутативным $K$):
$
  Aut R=((Jc dot Zc) ⋋ Dc) ⋋ Ah(K).
$

#lemma[
  Для кольца $R$ типа $D_n$ ($n>=4$) имеем $St subset.eq Aut R$. Кроме того,
  включение $Dc Ah(K)Zc subset.eq Aut R$ выполняется для кольца $R$ любого типа.
] <lem:l2018-enveloping-standard-automorphisms>

Группа автоморфизмов кольца Ли $N Phi(K)$ и группа $Aut R$ для типов $B_n$,
$C_n$ и $D_n$ действуют одинаково по модулю $R^2$ при $n>4$, учитывая описание
$Aut N Phi(K)$ в [@bib:l2018-enveloping-Levchuk2016; теоремы
@th:l2016-hypercentral-b-automorphisms и @th:l2016-hypercentral-d-automorphisms]
и леммы @lem:l2018-enveloping-lie-automorphisms,
@lem:l2018-enveloping-standard-automorphisms. В частности, группа $Aut R$ типа
$D_n$ при $n>4$ действует по модулю $R^2$ как произведение $Dc Ah(K)St$.

Автоморфизмы кольца Ли $N Phi(K)$ типа $D_4$ описаны в
[@bib:l2018-enveloping-Levchuk1990, I, теорема~@th:l1990-small-d4-lie]. Здесь
произвольный автоморфизм действует по модулю $R^2$ как автоморфизм $hat(beta)$
алгебры Ли $N Phi(K)$, сопоставляемый в [@bib:l2018-enveloping-Levchuk1990]
определенным матрицам $beta=lr(||b_(u v)||)$ из $SL(3, K)$. К ним относятся
графовые автоморфизмы, соответствующие изометриям графа Кокстера системы корней
$Phi$, которые действуют как симметрическая группа подстановок степени $3$ на
простых корнях $r_1,r_2,r_3$ и фиксируют один простой корень $q$, где
$q+r_i in Phi$ для всех $i$. С учетом
предложения~@prop:l2018-enveloping-multiplication, можно считать $r_1=r$,
$r_2=overline(r)$, $overline(overline(r))=r$, так что
$
  e_q e_(r_i)=e_(q+r_i), quad e_(r_i)e_q=0, quad i=1,2;
  quad e_(r_3)e_q=e_(q+r_3), quad e_q e_(r_3)=0.
$

#source(5, printed: "рукопись 5")Тогда в кольце $R$ правый аннулятор
${alpha in R | R alpha=0}$ равен $K e_rho+K e_(r_3)$ и характеристичен. Поэтому
при $hat(beta) in Aut R$ матрица $beta$ имеет клеточно-треугольный вид и ее
верхняя диагональная $2 times 2$ клетка входит во множество
@eq:l2018-enveloping-symmetric-root-subgroup. Более того, используя также
$hat(beta)$-инвариантность соотношений $e_(r_1)e_q=e_(r_2)e_q=0$, получаем
включение $hat(beta) in Dc St$.

#lemma[
  Группа автоморфизмов $Aut R$ кольца $R$ действует по модулю $R^2$ как
  произведение $Dc Ah(K)St$ для типа $D_n$ ($n>=4$) и как $Dc Ah(K)$ для типов
  $B_n$ и $C_n$, $n>4$.
] <lem:l2018-enveloping-automorphisms-modulo-square>

Пусть $Ac_2$ — аннулятор в кольце $K$ элемента $2$ и $d_1,d_2,d_3 in Ac_2$.
Учитывая [@bib:l2018-enveloping-Levchuk1990], алгебра Ли $N D_4 lr((K))$
допускает гиперцентральный автоморфизм
$
  eta(d_1, d_2, d_3):e_q->e_q+sum_(m=1)^3 d_m e_(rho-q-r_m),
  quad e_(q+r_i)->e_(q+r_i)+d_i e_(rho-q), quad i=1,2,3.
$

#theorem[
  Группа автоморфизмов $Aut R$ обертывающего кольца $R$ алгебры Ли $N Phi(K)$
  типа $D_4$ допускает разложение
  $
    (((Zc times x_(rho-q-r_1) lr((K)) times x_(rho-q-r_2) lr((K)))
        ⋋ eta(Ac_2, Ac_2, Ac_2)) ⋋ (St Dc)) ⋋ Ah(K).
  $
] <th:l2018-enveloping-d4-automorphisms>

В группе автоморфизмов алгебр Ли $N Phi(K)$ классических типов в
[@bib:l2018-enveloping-Levchuk2016; § @sec:l2016-hypercentral-automorphisms]
выявлена подгруппа $V(Phi)$ гиперцентральных автоморфизмов высоты $>1$ (вместе с
тождественным). Положим $V_R lr((Phi))=V(Phi) inter Aut R$ и
$Jc_R=Jc inter Aut R$.

#theorem[
  Группа автоморфизмов обертывающего кольца $R$ алгебры Ли $N Phi(K)$
  классического типа допускает разложение
  $
    Aut R=((Zc V_R lr((Phi)) Jc_R) ⋋ (St Dc)) ⋋ Ah(K)
    quad "для типа" D_n quad (n>=4),
  $
  $
    Aut R=((Zc V_R lr((Phi)) Jc_R) ⋋ Dc) ⋋ Ah(K)
    quad "для типов" B_n "и" C_n quad (n>4).
  $
] <th:l2018-enveloping-classical-automorphisms>
