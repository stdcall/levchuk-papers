#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== #[ ] <sec:l1983-dickson-projective-action>

В исследовании группы $PSL_2 lr((q))$ в [@bib:l1983-dickson-Dickson1901] важную
роль играет её представление дважды транзитивной группой подстановок.
Аналогичное представление мы рассматриваем и в случае, когда основное поле
произвольно.

Пусть $z in F$. Совокупность $F^((z))$ всех унипотентных матриц
$alpha=lr(||a_(i j)||)$ из группы $SL_2 lr((F))$ (т.~е. матриц со следом
$a_(11)+a_(22)=2$) таких, что
$
  (a_(21)z+a_(22))z=a_(11)z+a_(12),
$ <eq:l1983-dickson-projective-fixed-point>
есть подгруппа, как показывают равенства $F^((z))=tau_z F^((0))tau_(-z)$,
$F^((0))=tau'_F$. Для унипотентной матрицы $alpha=lr(||a_(i j)||)$, не лежащей в
$tau_F=F^((infinity))$, уравнение @eq:l1983-dickson-projective-fixed-point имеет
единственный корень $z=(1-a_(22))/a_(21)$. След произведения двух унипотентных
матриц, отличных от единичной матрицы $epsilon$ и выбранных в подгруппах
$F^((a))$ и $F^((b))$, не равен 2 (достаточно рассмотреть случай $b=infinity$).
#source(3, printed: 423)Отсюда вытекает следующее утверждение:

#property[
  Всякая неединичная подгруппа унипотентных матриц из $SL_2 lr((F))$, где $F$ —
  поле, лежит в единственной подгруппе вида $F^((a))$,
  $a in F union {infinity}$; в частности, $F^((a)) inter F^((b))=1$ при
  $a != b$.
] <prop:l1983-dickson-unipotent-partition>

Положим $tilde(F)=F union {infinity}$, $Omega={F^((a)) | a in tilde(F)}$. В силу
@prop:l1983-dickson-unipotent-partition) произвольной матрице
$beta=lr(||b_(i j)||) in GL_2 lr((F))$ соответствует подстановка
$hat(beta):F^((a))->beta F^((a)) beta^(-1)=F^((b))$ множества $Omega$ и,
следовательно, подстановка $pi_beta:a->b$ множества $tilde(F)$. Подстановку
$pi_beta$ можно определить также формулой
$pi_beta lr((z))=(b_(11)z+b_(12))/(b_(21)z+b_(22))$, накладывая при этом на
символ $infinity$ условия $pi_beta lr((infinity))=b_(11)/b_(21)$ и
$infinity=a/0=infinity/a=a infinity=infinity a=a+infinity=infinity+a$,
$a/infinity=0$, $a in F^hash$. Отображения $beta->pi_beta$ и $beta->hat(beta)$
являются гомоморфизмами группы $GL_2 lr((F))$ в группу подстановок множества
$tilde(F)$ и соответственно $Omega$ с одним и тем же ядром, подгруппой скалярных
матриц $a epsilon$, $a in F^hash$. По определению, $beta(z)=pi_beta lr((z))$ при
всех $beta in GL_2 lr((F))$, $z in tilde(F)$.

В группе $L=PSL_2 lr((F))$ всегда можно выбрать подстановку $alpha$, переводящую
наперёд заданные символы $a,b in tilde(F)$ соответственно в $0,infinity$; в
явном виде $alpha$ записывается так же, как и при $F=GF(q)$ в
[@bib:l1983-dickson-Dickson1901, §239]. Поэтому выполняются свойства

#property[
  Группа $L=PSL_2 lr((F))$ действует, как дважды транзитивная группа подстановок
  на множестве $tilde(F)=F union {infinity}$, а следовательно, и на множестве
  ${F^((a)) | a in tilde(F)}$.
] <prop:l1983-dickson-two-transitive>

#property[
  Подгруппа $F^((a))$ ($a in tilde(F)$) транзитивна на множестве
  $tilde(F) without {a}$.
] <prop:l1983-dickson-root-group-transitive>

#property[
  Совокупность подстановок из $L$, фиксирующих единственный символ
  $a in tilde(F)$, совпадает с $F^((a)) without {epsilon}$.
] <prop:l1983-dickson-unique-fixed-point>

#property[
  Стабилизатор в $L$ любых трёх точек единичен.
] <prop:l1983-dickson-three-point-stabilizer>

Свойства @prop:l1983-dickson-root-group-transitive),
@prop:l1983-dickson-unique-fixed-point) очевидны при $a=infinity$; в силу
@prop:l1983-dickson-two-transitive) они справедливы при любом $a in tilde(F)$.
Свойство @prop:l1983-dickson-three-point-stabilizer) следует из того, что
уравнение @eq:l1983-dickson-projective-fixed-point имеет в $tilde(F)$ не более
двух корней.

Стабилизатор в $L$ одной точки $a$ или двух точек $a,b$ из $tilde(F)$ обозначаем
соответственно через $L^((a))$ и $L^((a,b))$. Очевидно, что
$L^((0,infinity))=delta_(F^hash)={delta_t | delta_t=mat(t, 0; 0, t^(-1)),
  t in F^hash}$, $L^((infinity))=tau_F ⋊ delta_(F^hash)$.

#property[
  Группа $L^((infinity))$ есть группа Фробениуса с ядром $tau_F$; всякая её
  абелева подгруппа лежит либо в $tau_F$, либо в $L^((mu,infinity))$,
  $mu != infinity$.
] <prop:l1983-dickson-affine-frobenius>

Отображение $a->tau_a$, очевидно, есть изоморфизм аддитивной группы поля $F$ на
группу $tau_F$. Отображение $t->delta_t$ мультипликативной группы $F^hash$ в $L$
является гомоморфизмом с ядром $lr(chevron.l -1 chevron.r)$.

#lemma[
  #source(4, printed: 424)Пусть $V$ — ненулевая аддитивная подгруппа поля $F$, а
  $F_V$ — наибольшее подкольцо в $F$, над которым $V$ является модулем, т.~е.
  $F_V={a in F | a V subset V}$. Тогда нормализатор подгруппы $tau_V$ в $L$
  совпадает с $tau_F ⋊ delta_(sqrt(F_V^hash))$; по определению, если
  $A subset F$, то $sqrt(A)={b in F | b^2 in A}$.
] <lem:l1983-dickson-normalizer>

#proof[
  В силу равенства $alpha L^((z))alpha^(-1)=L^((alpha(z)))$ и
  @prop:l1983-dickson-unipotent-partition), нормализатор $N_L lr((tau_V))$
  содержится в $L^((infinity))$. Остаётся применить равенства
  $delta_t tau_a delta_t^(-1)=tau_(a t^2)$.
]

#lemma[
  Пусть $Gamma$ — подгруппа группы $L^((infinity))$ такая, что
  $Gamma inter tau_F=tau_V != 1$, $Gamma inter delta_(F^hash)=delta_A != 1$. Она
  является группой Фробениуса с ядром $tau_V$ тогда и только тогда, когда
  $1-A^2 subset F_V^hash union {0}$. Для дополняемости подгруппы $tau_V$ в
  $Gamma$ достаточно условие
  ${a in (F without V) | a frak(J) subset V}=emptyset$, где $frak(J)$ — идеал
  подкольца $F_V$, порождённый множеством $1-A^2={1-a^2 | a in A}$.
] <lem:l1983-dickson-affine-frobenius>

#proof[
  Подгруппа $tau_V$ нормальна в $Gamma$, причём фактор-группа
  $Gamma/tau_V ≃ (Gamma tau_F)/tau_F$ абелева. Поэтому, когда $Gamma$ есть
  группа Фробениуса с ядром $tau_V$, её подгруппа $delta_A$ должна являться
  неинвариантным множителем, в силу @prop:l1983-dickson-affine-frobenius) и
  условия $delta_A != 1$. Свойство @prop:l1983-dickson-three-point-stabilizer) и
  равенство $tau_b L^((0,infinity)) tau_b^(-1)=L^((b,infinity))$ показывают, что
  подгруппа $delta_A$ всегда имеет единичные пересечения с подгруппами,
  сопряжёнными с нею в $L^((infinity))$. По лемме~@lem:l1983-dickson-normalizer,
  произвольный элемент $Gamma$ имеет вид $beta=tau_c delta_t$, где
  $t in sqrt(F_V^hash) subset F$. Так как коммутатор
  $[beta,delta_A]=tau_(c(1-A^2))$ лежит в $tau_V$, то справедливо последнее
  утверждение леммы. В частности, разложимость $Gamma=tau_V ⋊ delta_A$
  обеспечивается условием $1-A^2 subset F_V^hash union {0}$. Последнее
  необходимо для того, чтобы подгруппа $Gamma$ являлась группой Фробениуса, как
  показывают равенства $tau_b (tau_c delta_t) tau_(-b)=tau_(c+b(1-t^2))delta_t$.
  Они показывают также, что при условии $1-A^2 subset F_V^hash union {0}$ каждый
  элемент из $Gamma without tau_V$ будет $tau_V$-сопряжён с элементом из
  $delta_A$ и, следовательно, $Gamma$ будет являться группой Фробениуса. Лемма
  доказана.
]

С использованием свойств @prop:l1983-dickson-unipotent-partition),
@prop:l1983-dickson-two-transitive), @prop:l1983-dickson-unique-fixed-point) и
леммы~@lem:l1983-dickson-normalizer просто доказывается

#lemma[
  Всякая неприводимая подгруппа группы $PGL_2 lr((F))$, содержащая унипотентный
  элемент, не равный единице, с точностью до сопряжения в $L=PSL_2 lr((F))$
  имеет неединичные пересечения с подгруппами $tau_F$ и $tau'_F$, а с точностью
  до сопряжения в $PGL_2 lr((F))$ она #source(5, printed: 425)удовлетворяет
  условию @eq:l1983-dickson-normalization.
] <lem:l1983-dickson-irreducible-normalization>
