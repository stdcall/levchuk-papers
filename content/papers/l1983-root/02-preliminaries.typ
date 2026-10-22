#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== #[ ] <sec:l1983-root-preliminaries>

Наряду с группами Шевалле $Phi(K)$, будем рассматривать также группы Стейнберга
$#twisted($n$, $Phi$) _sigma (K)$, где $rho(Phi)=1$. С группой Стейнберга
связаны симметрия $r -> overline(r)$ порядка $n$ системы корней $Phi$ и
автоморфизм $t -> overline(t)$ кольца $K$; мы не исключаем того, что автоморфизм
$overline(t)$ тривиален на $K$, и обозначаем его централизатор в $K$ через
$K_sigma$. Если $a in #twisted($n$, $Phi$)$ — класс эквивалентности типа
$A_1 times A_1$ (или $A_1 times A_1 times A_1$) и $r$ — фиксированный, например,
наименьший корень из $a$, то отображение
$x_a: u -> x_r lr((u)) x_(overline(r)) lr((overline(u)))$ (соответственно
$x_a: u -> x_r lr((u)) x_(overline(r)) lr((overline(u)))
x_(overline(overline(r))) lr((overline(overline(u))))$) по-прежнему является
изоморфизмом аддитивной группы $K^+$ на корневую подгруппу #source(
  3,
  printed: 506,
)$X_a$ из $#twisted($n$, $Phi$) _sigma (K)$. Когда $a={r}$ — класс
эквивалентности типа $A_1$, то $X_a=x_a lr((K_sigma))$, где
$x_a lr((u))=x_r lr((u))$, $u in K_sigma$. Классы других типов в
$#twisted($n$, $Phi$)$ не встречаются, если
$#twisted($n$, $Phi$) != #twisted($2$, $A_(2m)$)$. По лемме
@lem:l1982-parabolic-root-folding из [@bib:l1983-root-Levchuk1982]
$#twisted($n$, $Phi$)$ можно рассматривать как систему корней, таким образом
определены ранг $#twisted($n$, $Phi$)$ и число $rho(#twisted($n$, $Phi$))$. В
дальнейшем через $G(K)$ обозначается группа Шевалле типа $G=Phi$ или группа
Стейнберга типа $G=#twisted($n$, $Phi$) != #twisted($2$, $A_(2m)$)$.

Каждый набор $frak(A)={frak(A)_a | a in G}$ аддитивных подгрупп группы $K^+$ мы
связываем с набором подгрупп $x_a lr((frak(A)_a))$, $a in G$, группы $G(K)$.
Если при $a,b,a+b in G$ коммутант $[x_a lr((frak(A)_a)),x_b lr((frak(A)_b))]$
всегда лежит в произведении подгрупп $x_s lr((frak(A)_s))$ ($s=i a+j b in G$,
$i>0$, $j>0$) с регулярным упорядочением сомножителей, то $frak(A)$ называется
элементарным ковром типа $G$ над $K$. При $G=Phi$ это равносильно тому, что
$
  frak(A)_(i a+j b) supset C_(i j,a b) frak(A)_a^i frak(A)_b^j
  quad (a,b,i a+j b in Phi; quad i>0, quad j>0),
$ <eq:l1983-root-carpet-condition>
где $C_(i j,a b)$ — константы из коммутаторной формулы Шевалле. См. также
[@bib:l1983-root-Kourovka1980, вопрос 7.28] и [@bib:l1983-root-Levchuk1982,
§~@sec:l1982-parabolic-elementary-carpets].

#lemma[
  Пусть $M$ — подгруппа группы $G(K)$ над коммутативным кольцом $K$, причём
  $gcd(char K, d)=1$ для всех $d$, $1<=d<=rho(G)$. Тогда пересечения
  $M inter X_a=x_a lr((frak(A)_a))$, $a in G$, определяют элементарный ковёр
  типа $G$ над $K$.
] <lem:l1983-root-intersection-carpet>

#proof[
  Пусть $a,b,a+b in G$ и $l=l(a,b)$ — наибольшее число с условием $l=i+j$,
  $i a+j b in G$. Ясно, что $l>=2$, и если $l=2$, то
  $[M inter X_a,M inter X_b] subset M inter X_(a+b)$. При $l>2$ имеем
  $rho(G)>1$. Не теряя общности, можем считать, что ранг $G=2$,
  $a,b,a+b in G^+$. Когда $G=Phi$, в силу известных неравенств
  $1<=|C_(i j,r s)|<=rho(Phi)$ и в силу выбора кольца $K$, для всякой его
  аддитивной подгруппы $A$ имеем $C_(i j,r s) A=A$.

  При $Phi=G_2$ и $l>2$ возможны два случая: $l=3$ и $l=5$. Если $l=3$, то
  коммутант $[x_a lr((frak(A)_a)),x_b lr((frak(A)_b))]$ лежит в произведении
  $x_(a+b) lr((2 frak(A)_a frak(A)_b))
  x_(2a+b) lr((3 frak(A)_a^2 frak(A)_b))
  x_(a+2b) lr((3 frak(A)_a frak(A)_b^2))$. Коммутируя его с
  $x_a lr((frak(A)_a))$, получаем включения
  $frak(A)_a^2 frak(A)_b subset frak(A)_a frak(A)_a frak(A)_b
  =6 frak(A)_a frak(A)_a frak(A)_b subset frak(A)_(2a+b)$; коммутирование с
  $x_b lr((frak(A)_b))$ даёт $frak(A)_a frak(A)_b^2 subset frak(A)_(a+2b)$.
  Отсюда уже следует включение $2 frak(A)_a frak(A)_b subset frak(A)_(a+b)$, а
  вместе с ним и @eq:l1983-root-carpet-condition. В случае $l=5$ рассуждения
  аналогичны. Пусть $G$ — типа $#twisted($3$, $D_4$)$. К системе
  $#twisted($3$, $D_4$)$ приводит гомоморфизм системы корней $D_4$ на #source(
    4,
    printed: 507,
  )$G_2$, связанный с симметрией порядка 3 схемы Дынкина. Поэтому
  $rho(#twisted($3$, $D_4$))=rho(G_2)=3$ и коммутаторы, не лежащие в одной
  корневой подгруппе, имеют один из следующих двух видов:
  $
    [x_a lr((u)),x_b lr((t))]=x_(a+b) lr((plus.minus u t))
    x_(2a+b) lr((plus.minus u overline(u)t)) times
    x_(3a+b) lr((plus.minus u overline(u)overline(overline(u))t))
    x_(3a+2b) lr((plus.minus u overline(u)overline(overline(u))t^2)),
  $ <eq:l1983-root-triality-long-commutator>
  $
    [x_a lr((u)),x_(a+b) lr((v))]
    =x_(2a+b) lr((plus.minus (u overline(v)+overline(u)v))) times
    x_(3a+b) lr(
      (plus.minus (u overline(u)overline(overline(v))
          +overline(u)overline(overline(u))v
          +overline(overline(u))u overline(v)))
    )
    x_(3a+2b) lr(
      (plus.minus (u overline(v)overline(overline(v))
          +overline(u)overline(overline(v))v
          +overline(overline(u))v overline(v)))
    ),
  $ <eq:l1983-root-triality-short-commutator>
  где $u in frak(A)_a$, $v in frak(A)_(a+b)$,
  $t=overline(t) in frak(A)_b subset K_sigma$. Рассмотрим первый случай (второй
  случай аналогичен уже рассмотренному при $Phi=G_2$). Вычислим коммутатор
  $
    [[ [x_a lr((u)),x_b lr((t))],x_a lr((u))],x_a lr((u))]
    =[x_(2a+b) lr((plus.minus 2u overline(u)t)),x_a lr((u))]=
    x_(3a+b) lr(
      (plus.minus 2(u overline(u overline(u)t)
          +overline(u) overline(overline(u overline(u)t))
          +overline(overline(u))(u overline(u)t)))
    )
    =x_(3a+b) lr((plus.minus 6u overline(u)overline(overline(u))t)).
  $
  Коммутируя его с $x_b lr((t))$, получаем
  $x_(3a+2b) lr((plus.minus 6u overline(u)overline(overline(u))t^2))$.
  Следовательно, два последних сомножителя в
  @eq:l1983-root-triality-long-commutator лежат в $M$ и
  $[[x_a lr((u)),x_b lr((t))],x_a lr((u))]
  =x_(2a+b) lr((plus.minus 2u overline(u)t))g$, где $g in M$. Поэтому второй
  сомножитель, а вместе с ним и все сомножители в произведении
  @eq:l1983-root-triality-long-commutator лежат в $M$.

  В случае, когда $G$ типа $#twisted($2$, $A_3$)$, требуется показать, что в
  разложении коммутатора
  $
    [x_a lr((u)),x_b lr((t))]=x_(a+b) lr((plus.minus u t))
    x_(2a+b) lr((plus.minus u overline(u)t))
    quad (u in frak(A)_a, quad t in frak(A)_b)
  $ <eq:l1983-root-unitary-commutator>
  сомножители также лежат в $M$. Коммутируя его с $x_a lr((u))$, получаем
  $x_(2a+b) lr((plus.minus (u t overline(u)+overline(u t)u))) in M$. Так как
  $t=overline(t)$ и $rho(#twisted($2$, $A_3$))=rho(B_2)=2$, то элементы
  $2u overline(u)t$, $u overline(u)t$ должны лежать в #source(
    5,
    printed: 508,
  )$frak(A)_(2a+b)$. Отсюда вытекает и включение $u t in frak(A)_(a+b)$.
  Проведённые рассуждения применимы и для доказательства случая $G=B_2$; нужно
  лишь заменять $overline(u)$ на $u$. Лемма доказана.
]

Ограничение на характеристику кольца $K$ в
лемме~@lem:l1983-root-intersection-carpet (когда $K$ — поле, оно равносильно
тому, что $rho(G)=1$ или $1<rho(G)<char K$) существенно. В частности, это
показывает пример группы $lr(chevron.l x_a lr((1)), x_b lr((1)) chevron.r)
subset B_2 lr((2))$, где ${a,b}$ — база в $Phi=B_2$. См. также
[@bib:l1983-root-Levchuk1982, пример @exm:l1982-parabolic-b2-quasinet].
