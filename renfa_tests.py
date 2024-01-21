from nfa import NFA
from renfa import E

NFA.clear()

NFA.visutext("Thompson Example from Lectures")
eg_lec = (E("ab") | E("")).star().show_all()

for w in eg_lec[:100]: assert w in eg_lec
eg_lec.nfa.run("abab") # slight rendering problems with epsilon

NFA.visutext("Simplify Expressions (Exercise)")

a, b, eps = E("a"), E("b"), E("")

triple = ( a | a+a | a+a+a ).star().show()
mystery = ( eps | a.star()+(b+a.star()).star()+b )+a.star()
mystery.show()
mystery2 = ( eps | a.star()+( eps | b+(a.star()+b).star()+a.star() )+b )+a.star()
mystery2.show()

ba_BA = (E("aa") | E("bb") |
         ( (E("ab") | E("ba")) +  (E("aa") | E("bb")).star() + (E("ab") | E("ba")) )).star()
ba_BA.show()

NFA.spec("""
AB
AB
AB a aB b Ab
aB a AB b ab
ab a Ab b aB
Ab a ab b AB
""").named("even numbers of a and b").visu()

NFA.visutext("Rational Identities (Exercise)")

α, β = E("α"), E("β")

ident_11 = (α|β).star().show()
ident_12 = (α.star() | β.star()).show()

NFA.VISULANG=6
ident_21 = ( (α+β).star() + α ).show()
ident_22 = ( α+(β+α).star() ).show()

ident_31 = ( (α+β | α).star() + α ).show()
ident_32 = ( α+(β+α | α).star() ).show()

NFA.visutext("Surprise Exam")

sexam = ( eps | b+a.star() ).show_all()



NFA.pdf_renderer.print_status()