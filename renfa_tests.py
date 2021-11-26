from nfa import NFA
from renfa import E

NFA.clear()

NFA.visutext("Thompson Example from Lectures")
eg_lec = (E("ab") | E("")).star().show_all()

NFA.visutext("A very horrible rat. exp. (Exercise)")
eg_horrible = ( E("aa") | E("bb") |
                ( (E("ab") | E("ba")) +  (E("aa") | E("bb")).star() + (E("ab") | E("ba")) ) ).star()
eg_horrible.show_all()

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