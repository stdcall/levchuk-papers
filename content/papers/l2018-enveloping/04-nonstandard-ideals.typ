#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== #[ ] <sec:l2018-enveloping-nonstandard-construction>

Построим нестандартный идеал $H$ обертывающей алгебры $R$ типа $D_n$ над полем
$K$ с $Lc=Lc(H)={r_1,r_2,dots,r_m}$ и $r_1=s$, $r_2=overline(s)$. С учетом
предложения~@prop:l2018-enveloping-multiplication, существуют неинцидентные с
$s$ и $overline(s)$ простые корни $p_i=overline(p_i)$ с условиями
$
  s_i=s+p_1+p_2+dots+p_i in Phi^+,
  quad e_(p_(i+1))e_(s_i)=e_(s_(i+1)), quad 1<=i<n-ht(s).
$

Пусть $p$ — инцидентный с $s$ простой корень, $p!=overline(p)$, а
$p_0=overline(p_0)$ — простой корень с условием $p+p_0 in Phi^+$. В силу
теоремы~@th:l2018-enveloping-ideal-corners, получаем
$T(s_0+overline(p)) subset H$, где полагаем $s_0=s$, если $s!=p$, и $s_0=s+p_0$,
если $s=p$. Если $Lc':=Lc without {s,overline(s)}$, то $Q(Lc') subset H$, причем
для наименьшего номера $k<n-ht(s)$ с условием $Q(s_k) subset H$ в $Lc'$ нет
корней, инцидентных корню $s_k$. Кроме того,
$
  H/(H inter Q(Lc)) tilde.eq (H+Q(Lc))/Q(Lc),
  quad Q(Lc)+H=Q(Lc)+Fc(H).
$

Полагая $t=dim_K H/(H inter Q(Lc))$, выберем базу $sum_(j=1)^m a_(i j)e_(r_j)$
($1<=i<=t$) фрейма $Fc(H)$, представляющую базу $H/(H inter Q(Lc))$;
упорядочение $Lc$ фиксируем.
#ed-note[Чистые проекции фрейма не обязаны принадлежать $H$. Действительные
  подъёмы базы фактора в $H$ учитывают дополнительные слагаемые в
  формуле~@eq:l2018-enveloping-ideal-basis.]
Тогда для однозначно определенных номеров $j_1=1<j_2<dots<j_t<=m$ можно считать
$
  a_(12)=c!=0, quad a_(i,j_i)=1 quad (1<=i<=t),
  quad a_(i k)=0 quad (k<j_i),
  quad a_(i,j_k)=0 quad (1<=i<k<=t).
$ <eq:l2018-enveloping-echelon-frame>

Выбранная $t times m$-матрица $lr(||a_(i j)||)$ ранга $t$ над $K$ определяет
пересечение
$
  H inter Q(Lc)=T(s_0+overline(p))+Q(s_k)+Q(overline(s)_k)
  +sum_(j=1)^k K(e_(s_j)+c e_(overline(s)_j))+sum_(j=3)^m Q(r_j)
$ <eq:l2018-enveloping-ideal-intersection>
(последнее слагаемое при $m=2$ отбрасываем). База по его модулю в $H$
записывается сейчас для подходящих элементов $d_j in K$ ($1<=j<=t$) в виде
$
  alpha_i=sum_(j=1)^m a_(i j)e_(r_j)+d_i e_(s_k), quad i=1,2,dots,t.
$ <eq:l2018-enveloping-ideal-basis>

#theorem[
  В алгебре $R$ типа $D_n$ ($n>=4$) всякий нестандартный идеал $H$ с множеством
  углов $Lc=Lc(H)={r_1=s,r_2=overline(s),r_3,dots,r_m}$, $1<=ht(s)<n-1$,
  однозначно представляется в виде $H=(H inter Q(Lc))+sum_(i=1)^t K alpha_i$ для
  пересечения $H inter Q(Lc)$ вида @eq:l2018-enveloping-ideal-intersection и
  базы @eq:l2018-enveloping-ideal-basis по его модулю в $H$ с условием
  @eq:l2018-enveloping-echelon-frame.
] <th:l2018-enveloping-nonstandard-ideals>
