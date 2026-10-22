#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== #[ ] <sec:l1983-root-main-results>

Пусть $frak(A)$ — элементарный ковер типа $Phi$ над периодическим полем $K$.
Определим для него множества $Sigma=Sigma(frak(A))$ и
$Sigma_+=Sigma_+ lr((frak(A)))$, как в
лемме~@lem:l1983-root-unipotent-reduction. Так как всякий унипотентный
элементарный ковер является допустимым по лемме
@lem:l1982-parabolic-admissible-carpet-triple-product из
[@bib:l1983-root-Levchuk1982], то при $Sigma=emptyset$, по
лемме~@lem:l1983-root-unipotent-reduction, $frak(A)$ — допустимый ковер. При
$Sigma!=emptyset$ мы можем представить $Sigma$ как объединение попарно
ортогональных неразложимых квазизамкнутых подсистем корней
$Sigma_1,Sigma_2,dots,Sigma_m$. Если $frak(A)$ — допустимый ковер, то в силу
леммы~@lem:l1983-root-periodic-rank-one и теоремы~@th:l1983-root-main
выполняется условие:

\*) для каждого $i$, $1<=i<=m$, и $r in Sigma_i$ существуют подполе $P_i$ и
элемент $t_r in K^hash$ такие, что $frak(A)_r=t_r P_i$, причем если
$"ранг" Sigma_i=1$, $Sigma_i={r,-r}$, то либо $t_r t_(-r) in P_i$, либо
$abs(P_i)=3$, $(t_r t_(-r))^2=-1$, либо $abs(P_i)=2$.

#source(12, printed: 515)Легко убедиться, что верно и обратное: элементарный
ковер $frak(A)$ типа $Phi$ над $K$ с условием \*) является допустимым. Таким
образом, мы получили решение частного случая вопроса 7.28 из
[@bib:l1983-root-Kourovka1980], когда $K$ — периодическое поле.

#remark[
  При рассмотрении вопроса 7.28 из [@bib:l1983-root-Kourovka1980] в
  [@bib:l1983-root-VavilovPlotkin1982, с. 67] указано: «Очевидно, что
  конструкция сетевой подгруппы $Gamma(sigma)$, предложенная в
  [@bib:l1983-root-VavilovPlotkin1979], дает ответ на этот вопрос (достаточно
  сравнить доказательство леммы 1 работы [@bib:l1983-root-Vavilov1978] с
  теоремой 1 работы [@bib:l1983-root-VavilovPlotkin1979])». Приведенное
  утверждение ошибочно. Действительно, работы
  [@bib:l1983-root-VavilovPlotkin1979; @bib:l1983-root-Vavilov1978] связаны с
  частным случаем вопроса 7.28: подгруппа $Gamma(sigma)$ определяется в них
  «сетью идеалов», т.~е. определенным элементарным ковром идеалов (см. лемму
  @lem:l1982-parabolic-nets-and-elementary-carpets
  из [@bib:l1983-root-Levchuk1982]). Последние всегда являются допустимыми
  коврами и, конечно, ответ на вопрос 7.28 в этом частном случае известен. (В
  лемме~@lem:l1982-parabolic-admissible-carpet-triple-product из
  [@bib:l1983-root-Levchuk1982] описана даже более общая ситуация.) По-видимому,
  недоразумение вызвано тем, что вопрос 7.28 из [@bib:l1983-root-Kourovka1980]
  воспроизведен в [@bib:l1983-root-VavilovPlotkin1982] в искаженном виде. При
  этом, подменяя вопрос об условиях существования подгруппы $Gamma(sigma)$
  вопросом ее построения, авторы [@bib:l1983-root-VavilovPlotkin1982] ошибочно
  считают, что всякий элементарный ковер аддитивных подгрупп также является
  допустимым. Соответствующие контрпримеры легко строятся и отмечаются в
  [@bib:l1983-root-Levchuk1982] (см. также
  лемму~@lem:l1983-root-periodic-rank-one выше). Пользуясь случаем, отметим, что
  на с. 522 работы [@bib:l1983-root-Levchuk1982] в строках 8 и 13 вместо второй
  формулы должно быть соответственно «любой ее надгруппе $Gamma$, для которой
  $Gamma inter H^L lr((K))=A inter H^L lr((K))$» и «любой ее надгруппе $Gamma$,
  для которой $Gamma inter H_sigma^L lr((K))=
  A inter H_sigma^L lr((K))$».
] <rem:l1983-root-question>

=== #[ ] <sec:l1983-root-steinberg>

Подгруппа $lr(chevron.l X_a, X_(-a) chevron.r)$ группы Стейнберга
$#twisted($n$, $Phi$) _sigma lr((K))$ есть гомоморфный образ группы
$SL_2 lr((K_sigma))$ (или $SL_2 lr((K))$), если $a in #twisted($n$, $Phi$)$ —
класс эквивалентности типа $A_1$ (соответственно $A_1 times A_1$ или
$A_1 times A_1 times A_1$). Поэтому с помощью
леммы~@lem:l1983-root-periodic-rank-one можно перенести результаты
§~@sec:l1983-root-periodic на группы Стейнберга
$#twisted($n$, $Phi$) _sigma lr((K))!=#twisted($2$, $A_(2k)$) lr((K))$. Если
здесь $"ранг" #twisted($n$, $Phi$)=2$, то
$#twisted($n$, $Phi$)=#twisted($3$, $D_4$)$ или $#twisted($2$, $A_3$)$.

Пусть $M$ — подгруппа группы $#twisted($3$, $D_4$) lr((K))$, пересечения которой
$M inter X_s=x_s lr((frak(A)_s))$, $s in #twisted($3$, $D_4$)$, неединичны и
порождают $M$. Пусть также ${a,b}$ — база системы $#twisted($3$, $D_4$)$, где
$b$ — класс типа $A_1$. С точностью до сопряжения элементом
$h(chi) in Aut #twisted($3$, $D_4$) lr((K))$ можем считать, что
$1 in frak(A)_a inter frak(A)_b$. Допустим, что подгруппа
$lr(chevron.l M inter X_b, M inter X_(-b) chevron.r)$ — периодическая. Используя
коммутаторные соотношения
$
  [[x_a lr((u)),x_b lr((t))],x_b lr((1))]
  =x_(3a+2b) lr((u overline(u) overline(overline(u)) t))
$
и @eq:l1983-root-triality-long-commutator, #source(13, printed: 516)получаем
включение $1 in frak(A)_(3a+2b)$, а затем, как и в §~@sec:l1983-root-periodic,
равенства $frak(A)_s=P$ для всех классов $s$ типа $A_1$; через $P$ и $F$
обозначаются соответственно $frak(A)_b$ и $frak(A)_a$. Кроме того, справедливо
включение
$F_sigma^3 subset {u overline(u) overline(overline(u)) | u in F} subset P$. Из
соотношений @eq:l1983-root-triality-long-commutator,
@eq:l1983-root-triality-short-commutator несложно вытекает равенство
$overline(F)=F$. Далее ограничимся рассмотрением исключительных случаев, когда
$char K=2$ или $3$. Как и в случае $M subset G_2 lr((K))$, при $char K=3$ для
всех классов $r$ типа $A_1 times A_1 times A_1$ находим равенство $frak(A)_r=F$,
а также включения $2P=P subset F_sigma$. По
лемме~@lem:l1983-root-periodic-rank-one, $P$ — периодическое поле, а соотношения
$F_sigma^3 subset P subset F_sigma$ доказывают периодичность поля $F$ и
равенства $F_sigma=P$, $M=#twisted($3$, $D_4$) lr((F))$. При $char K=2$ имеем
$
  [[x_(a+b) lr((F)),x_a lr((1))],x_b lr((1))]
  ={x_(3a+2b) lr((u+overline(u)+overline(overline(u)))) | u in F}
  subset M,
$
откуда $3F_sigma=F_sigma subset P$. Включение
$[x_a lr((F)),x_b lr((1))] subset M$ сейчас дает
${x_(2a+b) lr((overline(u) overline(overline(u)))) | u in F} subset M$,
$1 in frak(A)_(2a+b)$, и поэтому $frak(A)_r=F$ для всех классов $r$ типа
$A_1 times A_1 times A_1$. Далее, как и при $M subset G_2 lr((K))$, находим
$P subset F_sigma$, откуда $P=F_sigma$ и $M=#twisted($3$, $D_4$) lr((F))$.

По аналогии с $M subset B_2 lr((K))$ рассматривается и периодическая подгруппа
$M subset #twisted($2$, $A_3$)$. Так как в неразложимой системе
$#twisted($n$, $Phi$)!=#twisted($2$, $A_(2k)$)$ ранга $>=2$ каждый класс
эквивалентности содержится в подсистеме типа $#twisted($3$, $D_4$)$ или типа
$#twisted($2$, $A_3$)$, то отсюда вытекает

#theorem[
  Пусть $M$ — периодическая подгруппа группы Стейнберга
  $#twisted($n$, $Phi$) _sigma lr((K))!=#twisted($2$, $A_(2m)$) lr((K))$ над
  полем $K$. Допустим, что пересечения $M inter X_a$,
  $a in #twisted($n$, $Phi$)$, неединичны и порождают $M$, причем
  $"ранг" #twisted($n$, $Phi$)>=2$. Тогда для некоторого подполя $F subset K$ и
  диагонального элемента $h(chi) in Aut #twisted($n$, $Phi$) lr((K))$ имеем
  $F=overline(F)$ и $h(chi)M h(chi)^(-1)=#twisted($n$, $Phi$) _sigma lr((F))$.
] <th:l1983-root-steinberg>
