#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

#source(8, printed: 428)подкольцо поля $F$ и, следовательно, подполе. Подгруппа
$sqrt(F_V^hash)={a in F | a^2 in F_V^hash}$ группы $F^hash$ лежит в конечном
расширении поля $F_V$ и потому является циклической группой, содержащей
$F_V^hash$ с индексом $<=2$. Поэтому справедливы неравенства
$ abs(F_V^hash)<=abs(V)-1<=abs(A)<=abs(sqrt(F_V^hash))<=2abs(F_V^hash). $
Они показывают, что $V$ есть 1-мерный $F_V$-модуль, т.~е. $V=F_V$. Поскольку
$abs(A)$ — делитель числа $abs(sqrt(V^hash))$, то либо $A=V^hash$, либо
$A=sqrt(V^hash)$. Таким образом, утверждения б), в) доказаны.

г) Допустим, что $A!=V^hash$, и, следовательно, $A=sqrt(V^hash)$,
$abs(A)=2abs(V^hash)$. Очевидно, что в этом случае $p>2$ и поле $F$ содержит
квадратичное расширение подполя $V$. По
лемме~@lem:l1983-dickson-affine-frobenius, $Gamma$ — группа Фробениуса с ядром
$tau_V$. Она имеет циклический неинвариантный множитель
$cal(D)=H inter L^((a,infinity))$ ($a in F$) четного порядка, в силу
изоморфизмов
$Gamma"/"tau_V ≃ Gamma tau_F"/"tau_F ≃ A"/"lr(chevron.l -1 chevron.r)$ и
свойства~@prop:l1983-dickson-affine-frobenius. Пусть $pi$ — инволюция из
$cal(D)$. Всякий элемент, нормализующий какую-либо из подгрупп $cal(D)$ и
$lr(chevron.l pi chevron.r)$, индуцирует подстановку на множестве
${a,infinity}$. Поэтому нормализаторы подгрупп $cal(D)$ и
$lr(chevron.l pi chevron.r)$ совпадают и содержат подгруппу $cal(D)$ с индексом
$<=2$. По лемме~@lem:l1983-dickson-coset-count число всех инволюций в
$H without Gamma$ не превосходит числа
$f abs(V)(abs(A)"/"2)=f abs(V) abs(V^hash)$ и, следовательно, меньше числа
$abs(H colon cal(D))-abs(V)=f abs(V)^2$ смежных классов по $cal(D)$ в
$H without Gamma$. Следовательно,
$
  abs(N_H lr((cal(D))))=abs(N_H lr((lr(chevron.l pi chevron.r))))
  =2abs(cal(D))=2abs(V^hash).
$
Когда $alpha=norm(a_(i j)) in H without Gamma$ — инволюция,
уравнение~@eq:l1983-dickson-coset-involution принимает вид
$ z t^2 a_(21)+(t^2-1)a_(11)=0. $
<eq:l1983-dickson-exceptional-involution>

Из него следует, что если смежный класс $Gamma alpha$ содержит инволюцию,
отличную от $alpha$, то $a_(11)"/"a_(21) in V$. По
лемме~@lem:l1983-dickson-involution-product, число $k$ таких смежных классов не
превосходит $abs(V)$ и в каждом из них, по лемме~@lem:l1983-dickson-coset-count,
не более $abs(A)"/"2=abs(V^hash)$ инволюций. Число остальных смежных классов по
$Gamma$ в $H without Gamma$ равно $abs(H colon Gamma)-k-1$. Поэтому число всех
инволюций в $H without Gamma$ не превосходит числа
$
  k abs(V^hash)+f abs(V)-k=k(abs(V)-2)+f abs(V)
  <=abs(V)(abs(V)-2+f).
$
С другой стороны, число инволюций в $H without Gamma$, сопряженных с $pi$, равно
$
  abs(H colon N_H lr((lr(chevron.l pi chevron.r))))-abs(V)
  =(1+f abs(V))abs(V)"/"2-abs(V)=abs(V)(f abs(V)-1)"/"2;
$
#source(9, printed: 429)в частности, $f$ — нечетное число. Отсюда
$(f abs(V)-1)"/"2<=abs(V)-2+f$, т.~е. $f<=2+frac(1, abs(V)-2)<=3$ и,
следовательно, $f=1$ или $f=3$.

При $f=3$ предыдущие неравенства превращаются в равенства, откуда $abs(V)=p=3$,
$abs(H)=60$, $N_H lr((lr(chevron.l pi chevron.r)))$ — четверная группа. Здесь
$H$ содержит единственный класс сопряженных инволюций. Каждая четверная
подгруппа совпадает с нормализатором в $H$ любой своей подгруппы порядка 2.
Поэтому $15=abs(H colon N_H lr((lr(chevron.l pi chevron.r))))$ инволюций из $H$
лежат в пяти четверных подгруппах, имеющих попарно тривиальные пересечения. Но
тогда нормализатор четверной подгруппы в $H$ имеет порядок 12 и не содержит
неединичных нормальных подгрупп группы $H$. Следовательно, поставив в
соответствие каждому элементу $beta in H$ подстановку, которую индуцирует
сопряжение элементом $beta$ на множестве четверных подгрупп, получаем изоморфизм
группы $H$ на подгруппу индекса 2 симметричной группы подстановок 5-й степени,
т.~е. на $A_5$. Очевидно, что элемент $z in F^hash$ можно выбрать так, что
$H inter tau'_F=lr(chevron.l tau'_z chevron.r)$ и при подходящем изоморфизме $H$
на $A_5$ элементы $tau_1$ и $tau'_z$ перейдут соответственно в подстановки
$sigma=(123)$ и $pi=(345)$ или $(234)$.

Допустим, что $pi=(234)$ и, следовательно, $sigma pi=(13)(24)$ — инволюция.
Тогда след матрицы $tau_1 tau'_z$ равен нулю, откуда $z=1$ и
$H supset lr(chevron.l tau_V, tau'_V chevron.r)=PSL_2 lr((3))$. Здесь подгруппа
$Gamma$ допускает разложение
$Gamma=tau_V ⋊ lr(chevron.l delta_i tau_a chevron.r)$, где $i,a in F$, $i^2=-1$.
Поэтому выбранный изоморфизм группы $H$ на $A_5$ переводит $delta_i tau_a$ в
одну из инволюций $theta_1=(12)(45)$, $theta_2=(13)(45)$, $theta_3=(23)(45)$,
нормализующих подгруппу $lr(chevron.l sigma chevron.r)$. Каждое из произведений
$pi theta_1 sigma^(-1)$, $pi theta_2 sigma$, $pi theta_3$ равно $(354)$.
Следовательно, смежный класс
$tau'_1 delta_i tau_a tau_V=delta_i tau'_(-1) tau_a tau_V$
группы $H$ содержит унипотентный элемент, т.~е. матрицу со следом
$plus.minus 2$. Отсюда $a in V plus.minus i$. С точностью до замены $i$ на $-i$,
получаем $Gamma ∋ mat(i, 1; 0, -i)=gamma$,
$H=lr(chevron.l PSL_2 lr((3)), gamma chevron.r)$. Этот случай реализуется, так
как порождающие элементы $tau_1$, $omega_1$, $gamma$ группы $H$ удовлетворяют
соотношениям
$
  tau_1^3=omega_1^2=gamma^2=(tau_1 omega_1)^3=(omega_1 gamma)^3
  =(tau_1 gamma)^2=1,
$
которые являются определяющими для группы $A_5$, согласно Муру (см.
[@bib:l1983-dickson-CoxeterMoser1980, с. 101]).

В случае, когда $pi=(345)$, подстановка $sigma pi sigma pi sigma=(14)(25)$
является инволюцией. Поэтому след матрицы
$
  tau_1 tau'_z tau_1 tau'_z tau_1
  =mat(z^2+1, z^2+z; z^2-z, z^2+1)=omega
$
равен нулю. Но тогда $z^2+1=0$ и $omega=omega_(z-1)$. Этот случай также
реализуется, #source(10, printed: 430)так как выполняющиеся здесь соотношения
$tau_1^3=omega^2=(tau_1 omega)^5=1$ являются определяющими для группы $A_5$.
Кроме того, $omega tau_1 omega=tau'_z$ и
$H=lr(chevron.l tau_1, tau'_z chevron.r)$.

д) Рассмотрим случай, когда $A^2=V^hash!=1$ и при $p>2$ также $f=1$.

При $p>2$ подгруппа $cal(D)=H inter L^((a,infinity))$, выбранная в г), сопряжена
при помощи элемента $alpha=tau_a$ с $delta_A$. Поскольку в группе
$H^alpha=alpha^(-1)H alpha$ диагональная подгруппа
$delta_A=H^alpha inter L^((0,infinity))!=1$ не совпадает с нормализатором (см.
г)), то $H^alpha$ содержит элемент $omega_t$ ($t in F^hash$). Так как
$H^alpha inter tau'_F=omega_t tau_V omega_t^(-1)!=1$, то к группе $H^alpha$
применимо утверждение а) леммы с $f=1$. Оно показывает, что
$H^alpha inter tau'_F=beta^(-1)alpha^(-1)(H inter tau'_F)alpha beta$
для некоторого $beta in tau_V$. Отсюда $alpha beta in L^((0)) inter tau_F=1$,
$alpha=beta^(-1) in H$, $H^alpha=H$. Итак, при $p>2$ должны иметь $H ∋ omega_t$
и $Gamma=tau_V ⋊ delta_A subset PGL_2 lr((V))$.

При $p=2$, по лемме~@lem:l1983-dickson-characteristic-two-dihedral, группа $H$
также содержит элемент $omega_t$, поэтому
$H inter tau'_F=omega_t tau_V omega_t^(-1)=tau'_(t^2 V)$. Так как здесь
$A^2=V^hash$, то
$omega_(t V) subset lr(chevron.l tau_V, tau'_(t^2 V) chevron.r) subset H$,
$delta_A=omega_(t V^hash) omega_(t V) subset H$ и, в силу
леммы~@lem:l1983-dickson-affine-frobenius,
$Gamma=tau_V ⋊ delta_(V^hash) subset PGL_2 lr((V))$.

В обоих случаях представителем произвольного смежного класса по $Gamma$ в
$H without Gamma$ можно взять инволюцию $alpha=norm(a_(i j))$ с условием
$lambda=a_(11)"/"a_(21) in V$. Ее существование при $p=2$ следует из утверждения
в) леммы и уравнения~@eq:l1983-dickson-exceptional-involution; при $p>2$ по
лемме~@lem:l1983-dickson-involution-product $alpha$ совпадает с одной из
инволюций $tau_b omega_t tau_b^(-1)=mat(b t^(-1), ∗; -t^(-1), -b t^(-1))$,
$b in V$. На самом деле, включение $a_(i j)"/"a_(21) in V$ выполняется для всех
элементов $a_(i j)$. В силу равенства $a_(11)+a_(22)=0$, это достаточно доказать
лишь для $a_(12)$. Ясно, что существует инволюция
$beta=norm(b_(i j)) in H without Gamma$, не лежащая в $Gamma alpha$. По
лемме~@lem:l1983-dickson-involution-product, $lambda_1=b_(11)"/"b_(21) in V$,
$lambda_1!=lambda$, и так как $Gamma alpha beta!=Gamma$, то
$
  frac(a_(11)b_(11)+a_(12)b_(21), a_(21)b_(11)+a_(22)b_(21))
  =frac((a_(11)lambda_1+a_(12))b_(21), (b_(11)-lambda b_(21))a_(21))
  =frac(lambda lambda_1+a_(12)a_(21)^(-1), lambda_1-lambda),
$
откуда $a_(12)"/"a_(21) in V$. Далее, элемент $a_(21)$ лежит в $A=sqrt(V^hash)$,
так как $a_(21)^(-2)=(a_(11)a_(22)-a_(12)a_(21))a_(21)^(-2) in V^hash$.
Следовательно, $(delta_A alpha) inter PSL_2 lr((V))!=emptyset$. Таким образом,
представитель каждого смежного класса по $Gamma$ в $H$ можно выбрать в
$PSL_2 lr((V))$. Отсюда $H inter tau'_V!=1$. Однако
$lr(chevron.l tau_V, tau'_a chevron.r)=PSL_2 lr((V))$ при любом $a in V^hash$.
Учитывая а), получаем
$H=lr(chevron.l PSL_2 lr((V)), delta_A chevron.r)=PGL_2 lr((V))$.

е) Рассмотрим $H$, когда $A=V^hash!=1$. При $p=2$ имеем $A^2=A=V^hash$ и, в силу
д), $H=PGL_2 lr((V))=PSL_2 lr((V))$. Пусть $p>2$. Выберем унипотентный элемент
$alpha=norm(a_(i j)) in H without Gamma$. Можно считать, что $a_(11)+a_(22)=2$ и
в силу в) уравнение @eq:l1983-dickson-coset-unipotent, принимающее сейчас вид
$z t a_(21)+ #source(11, printed: 431) (t-t^(-1))a_(11)=2-2t^(-1)$, для всякого
$t in V^hash$ имеет решение $z in V$. При $t=-1$ получаем $-z a_(21)=4$, откуда
$a_(21) in V$. В частности, $H inter tau'_F subset PSL_2 lr((V))$. Так как
группа $PSL_2 lr((V))$ совпадает с $lr(chevron.l tau_V, tau'_a chevron.r)$ при
любом $a in V^hash$, то она лежит в $H$. Учитывая
лемму~@lem:l1983-dickson-affine-frobenius, получаем
$Gamma=tau_V ⋊ delta_(V^hash)$. Далее, при $z in V$ унипотентный элемент
$tau'_z alpha tau'_(-z)=norm(b_(i j) lr((z)))$ лежит в $H$. По доказанному,
$V ∋ b_(21) lr((z))=a_(21)-z a_(22)+z(a_(11)-z a_(12))$. Полагая здесь $z=1$ и
$z=-1$, получаем соответственно равенства $a_(12)-2a_(11)=c_1$,
$a_(12)+2a_(11)=c_2$, где $c_1,c_2 in V$. Так как определитель
$abs(mat(1, -2; 1, 2))=4!=0$, то $a_(12),a_(11) in V$ и, следовательно,
$alpha in PSL_2 lr((V))$. В силу в) и произвола $alpha$ каждый смежный класс
группы $H$ по $Gamma$ лежит в $PSL_2 lr((V))$. Следовательно, $H=PSL_2 lr((V))$.

ж) Допустим, наконец, что $V^hash=1$ и, следовательно, $A^2=A=1$, $p=2$,
$Gamma=tau_V={epsilon,tau_1}$. Из доказательства а) следует, что $H$ содержит
$1+2f$ инволюций $tau_1=alpha_0,alpha_1,alpha_2,dots,alpha_(2f)$, и все они
сопряжены в $H$. Учитывая в), находим $H={alpha_i,beta_i | 0<=i<=2f}$, где
$beta_i=alpha_0 alpha_i$. Произвольный элемент $alpha_i beta_j$ является
инволюцией, сопряжение, переводящее $alpha_i$ в $alpha_0$, приводит его к виду
$alpha_0 beta_l=alpha_l$. Поэтому существует $k$, зависящее от $i$ и $j$, для
которого $alpha_i beta_j=alpha_k$ и, следовательно, $beta_i beta_j=beta_k$.
Равенства
$
  alpha_0 beta_m alpha_0=alpha_0(alpha_0 alpha_m)alpha_0
  =alpha_m alpha_0=beta_m^(-1),
$
$
  beta_j^(-1) beta_i^(-1)=beta_k^(-1)=alpha_0 beta_k alpha_0
  =(alpha_0 beta_i alpha_0)(alpha_0 beta_j alpha_0)
  =beta_i^(-1) beta_j^(-1)
$
показывают, что $M={beta_0,beta_1,dots,beta_(2f)}$ — абелева подгруппа индекса 2
в $H$. По лемме~@lem:l1983-dickson-characteristic-two-dihedral найдется матрица
$xi$ (вообще говоря, над квадратичным расширением поля $F$), для которой
$xi^(-1) M xi ∋ delta_t!=1$. Очевидно, что элемент $delta_t$ коммутирует лишь с
диагональными элементами, поэтому $xi^(-1) M xi$ — диагональная подгруппа.

Лемма доказана.
