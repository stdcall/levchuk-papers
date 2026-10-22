#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== #[ ] <sec:l1983-root-periodic>

#lemma[
  Если периодическая подгруппа группы $PSL_2$ над произвольным полем $K$ имеет
  неединичные пересечения
  $ mat(1, V; 0, 1), quad mat(1, 0; V', 1) $
  с подгруппами
  $ mat(1, K; 0, 1), quad mat(1, 0; K, 1) $
  соответственно, причем $V ∋ 1$, то она содержит элемент вида
  $ mat(0, t; -t^(-1), 0), $
  #source(9, printed: 512)$V$ есть периодическое подполе, а $V'$ либо совпадает
  с $V$, либо $abs(V)=3$, $V'=i V$, где $i in K$, $i^2=-1$, либо $abs(V)=2$,
  $V'=d V$, где $d$ — элемент из $K$, алгебраичный над $GF(2)$.
] <lem:l1983-root-periodic-rank-one>

См. [@bib:l1983-root-Levchuk1983Dickson, теорема
@th:l1983-dickson-classification и предложение
@prop:l1983-dickson-transcendental-free-product].

В применениях леммы~@lem:l1983-root-periodic-rank-one к группам Шевалле мы будем
использовать известный гомоморфизм группы $SL_2 lr((K))$ на подгруппу
$lr(chevron.l X_r, X_(-r) chevron.r) subset Phi(K)$, $r in Phi$, продолжающий
отображение
$
  mat(1, t; 0, 1) -> x_r lr((t)), quad
  mat(1, 0; t, 1) -> x_(-r) lr((t)).
$
Образы матриц
$ mat(t, 0; 0, t^(-1)), quad mat(0, t; -t^(-1), 0), $
где $t in K^hash$, обозначаются соответственно через $h_r lr((t))$,
$n_r lr((t))$. При этом для любых $r,s in Phi$, $u,t in K^hash$ имеем
$
  n_r x_s lr((u)) n_r^(-1)=x_(w_r lr((s))) lr((plus.minus u)), quad
  h_r lr((t)) x_s lr((u)) h_r lr((t))^(-1)=x_s lr((t^(A_(r s)) u)),
$ <eq:l1983-root-weyl-diagonal-action>
где $n_r=n_r lr((-1))$, $A_(r s)=frac(2lr((r,s)), lr((r,r)))$, $w_r$ — отражение
относительно корня $r$.

Исследуем подгруппу $M$ группы $Phi(K)$ над полем $K$ с неединичными
пересечениями $M inter X_r=x_r lr((frak(A)_r))$, $r in Phi$, и условием:

Б) существует $s in Phi$, при котором
$lr(chevron.l M inter X_s, M inter X_(-s) chevron.r)$ — периодическая подгруппа.

Если $rho(Phi)=1$ или $1<rho(Phi)<char K$, то, по
лемме~@lem:l1983-root-intersection-carpet, $frak(A)={frak(A)_r | r in Phi}$ —
элементарный ковер типа $Phi$. В силу леммы~@lem:l1983-root-periodic-rank-one,
$frak(A)_s frak(A)_(-s)=P$ — подполе в $K$. С помощью
леммы~@lem:l1983-root-rank-two-subfields получаем $frak(A)_r=chi(r)P$,
$r in Phi$, как и в следствии~@cor:l1983-root-algebraic-carpet.

Рассмотрим случаи, когда $"ранг" Phi=2$, $1<char K<=rho(Phi)$. Выберем базу
$Pi={a,b}$ так, что $2a+b in Phi$. Предположим, что
$1 in frak(A)_a inter frak(A)_b$; мы полагаем $frak(A)_a=F$, $frak(A)_b=P$.

При $Phi=G_2$ равенство
$[[x_a lr((F)),x_b lr((P))],x_b lr((P))]=x_(3a+2b) lr((F^3 P P))$
дает включения $frak(A)_(3a+2b) supset F^3 P P ∋ 1$. Допустим, что Б) выполнено
для длинного корня $s$. Так как длинные корни системы $Phi=G_2$ образуют
замкнутую подсистему корней типа $A_2$, то, по доказанному, $frak(A)_r=P$ и, по
лемме~@lem:l1983-root-periodic-rank-one, $n_r in M$ для всех длинных корней $r$.
При $char K=3$ короткие #source(10, printed: 513) корни из $Phi$ образуют
квазизамкнутую подсистему корней типа $A_2$. Всякий короткий корень $r$ в паре с
некоторым длинным корнем образует базу в $Phi$ и поэтому
$frak(A)_r^3 subset frak(A)_r^3 P P subset P$, в частности, $frak(A)_r$ лежит в
периодическом подполе, откуда $frak(A)_r=F$. Кроме того,
$M supset [[x_a lr((1)),x_b lr((P))],x_a lr((1))]=x_(2a+b) lr((2P))$, т.~е.
$P subset F$. Но периодические поля $F$ и $P$ с условием $F^3 subset P subset F$
совпадают. Пусть $char K=2$. Тогда
$
  [[n_b x_a lr((F)) n_b^(-1),x_a lr((1))],x_b lr((1))]
  =x_(3a+2b) lr((3F)),
$
откуда $F subset P$. Из включения $[x_a lr((F)),x_b lr((1))] subset M$ сейчас
следует, что $x_(2a+b) lr((F)) subset M$ и поэтому $frak(A)_r=F$ для всех
коротких корней. Учитывая включение $F subset P$, при $P^hash=1$ получаем $F=P$.
При $P^hash!=1$ замечаем, что $M supset h_b lr((P^hash))$. В силу включения
$M supset [x_a lr((1)),x_b lr((P))]$ подгруппа $M$ содержит также множество
${x_(a+b) lr((t)) x_(2a+b) lr((t^2)) | t in P^hash}$. Коммутируя его с
$h_b lr((P^hash))$, получаем $x_(a+b) lr((P(1-P^hash)))$. Поэтому
$P(1-P^hash)=P subset F$, т.~е. вновь $F=P$.

В случае, когда $M subset B_2 lr((K))$ и $char K=2$, потребуем, чтобы подгруппа
$M$ являлась периодической. Допустим, что $abs(M inter X_s)>2$ для какого-либо
длинного корня $s$; можно считать, что $s=b$. По
лемме~@lem:l1983-root-periodic-rank-one, $h_b lr((P^hash))$ и $n_b$ лежат в $M$.
Учитывая @eq:l1983-root-weyl-diagonal-action, получаем:
$n_b lr((M inter X_a)) n_b^(-1)=M inter X_(a+b)=x_(a+b) lr((F))$. Коммутируя
$h_b lr((P^hash))$ с $[x_a lr((F)),x_b lr((P))]$, получаем
$x_(a+b) lr((F P(1-P^hash)))$, откуда $F supset F P supset P$ и $abs(F)>=4$. По
лемме~@lem:l1983-root-periodic-rank-one выполняется также включение $n_a in M$.
В силу @eq:l1983-root-weyl-diagonal-action, для всех длинных корней $r$ получим
$frak(A)_r=P$, а для коротких корней $r$ — $frak(A)_r=F$. Так как $F$ —
периодическое поле, то $F^2=F$ и, как показано выше, $F supset P$. С другой
стороны, $P=frak(A)_(2a+b) supset F^2 P supset F^2$. Поэтому $F=P$. Далее, при
$abs(M inter X_a)>2$ подгруппа $h_a lr((F^hash))$ содержится в $M$, а ее
коммутант с $[x_a lr((F)),x_b lr((P))]$ равен
$x_(2a+b) lr((F^2 P(1-F^(hash 2))))$ и, в силу
@eq:l1983-root-weyl-diagonal-action, $abs(M inter X_b)>2$, т.~е. приходим к
рассмотренному случаю. Допустим, что $abs(M inter X_r)=2$, $frak(A)_r={0,t_r}$
для всех $r in Phi$. По лемме~@lem:l1983-root-periodic-rank-one, $M$ содержит
$n_a lr((alpha^(-1)))$ и $n_b lr((beta^(-1)))$ для некоторых элементов
$alpha,beta in K^hash$, алгебраических над $GF(2)$. Учитывая
@eq:l1983-root-weyl-diagonal-action, должны иметь $t_(-b)=beta^2$,
$t_(-a)=alpha^2$, $t_(a+b)=beta^(-1)$, $t_(2a+b)=alpha^(-2)$. Отсюда $M ∋ g_0$,
где #metadata(()) <pass:l1983-root-exceptional-b2-elimination>
$
  g_0=[[x_(-a) lr((alpha^2)),x_(2a+b) lr((alpha^(-2)))],x_a lr((1))]
  =x_(a+b) lr((alpha^2)) x_(2a+b) lr((alpha^2)).
$
Элементы $g_k=x_(a+b) lr((alpha^2 beta^(2k)))
x_(2a+b) lr((alpha^4 beta^(4k)))$, $k=1,2,dots$, также лежат в $M$, в силу
соотношений $[[g_(k-1),x_(-b) lr((beta^2))],x_b lr((1))]=g_k$. Однако существует
$k>=1$, при котором $beta^k=1$, следовательно,
$g_k=g #source(11, printed: 514)=x_(a+b) lr((alpha^2))
x_(2a+b) lr((alpha^4))$. Поэтому $x_(2a+b) lr((alpha^2+alpha^4))=g_0 g in M$.
Легко видеть, что если $alpha^2+alpha^4=0$, т.~е. $alpha=1$, то $M=B_2 lr((2))$.
Предположим, что $alpha^2+alpha^4!=0$ и, следовательно,
$alpha^2+alpha^4=alpha^(-2)$. Вычисления показывают:
$
  g'=[[[x_a lr((1)),x_b lr((1))],x_(-a) lr((alpha^2))],x_a lr((1))]
  =x_(a+b) lr((alpha^4)) x_(2a+b) lr((alpha^4));
$
$
  g g'=x_(a+b) lr((alpha^2+alpha^4)) in M, quad
  beta^(-1)=alpha^2+alpha^4=alpha^(-2);
$
$
  [[x_(-a) lr((alpha^2)),x_(2a+b) lr((alpha^(-2)))],
    [x_(a+b) lr((beta^(-1))),x_(-b) lr((beta^2))]]g'
$
$
  = [x_b lr((alpha^2)) x_(a+b) lr((1)),
    x_a lr((beta)) x_(2a+b) lr((1))]g'
  =x_(2a+b) lr((alpha^4+alpha^6)).
$
Отсюда $alpha^4+alpha^6=alpha^2+alpha^4=alpha^(-2)$ и, следовательно, $alpha=1$,
$M=B_2 lr((2))$.

Проведенные в этом параграфе рассуждения доказывают теорему~@th:l1983-root-main
для периодической подгруппы $M$ в случае, когда $"ранг" Phi=2$, а поэтому и
когда $"ранг" Phi>=2$, в силу неразложимости системы корней $Phi$. При условии
А) теорему~@th:l1983-root-main доказывают
лемма~@lem:l1983-root-intersection-carpet и
следствие~@cor:l1983-root-algebraic-carpet. Таким образом,
теорема~@th:l1983-root-main полностью доказана.

#remark[
  Из доказательства следует, что утверждения теоремы~@th:l1983-root-main
  остаются справедливыми, если заменить в ней условие периодичности подгруппы
  $M$ более слабым условием Б), но при этом либо $rho(Phi)=1$, либо
  $1<rho(Phi)<char K$, либо $Phi=G_2$ и в Б) $s$ — длинный корень.
] <rem:l1983-root-weaker-periodicity>
