package inference;

import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import connectives.*;
import formula.Formula;
import roles.InverseRole;

import java.util.ArrayList;
import java.util.List;

public class ConceptInference {

    public List<Formula> strongForgetting(AtomicConcept concept, List<Formula> formula_list){
        List<Formula> positive_formula_list = new ArrayList<>();
        List<Formula> negative_formula_list = new ArrayList<>();
        List<Formula> output_list = new ArrayList<>();
        FChecker fChecker = new FChecker();

        for (Formula formula: formula_list) {
            if (fChecker.positive(concept, formula) == 1) {
                positive_formula_list.add(formula);
            } else if (fChecker.negative(concept, formula) == 1) {
                negative_formula_list.add(formula);
            } else {
                output_list.add(formula);
            }
        }
        Formula substitution = getNegativeSubstitution(concept, positive_formula_list, output_list);
        if (substitution != null) {
            output_list.addAll(ackermannReplace(concept, negative_formula_list, substitution));
            return output_list;
        }else if ((substitution = getPositiveSubstitution(concept, negative_formula_list, output_list)) != null){
            output_list.addAll(ackermannReplace(concept, positive_formula_list, substitution));
            return output_list;
        }
        return null;
    }

    private Formula getNegativeSubstitution(AtomicConcept concept, List<Formula> positive_formula_list, List<Formula> output_list) {
        FChecker fChecker = new FChecker();
        List<Formula> temp_output_list = new ArrayList<>();
        List<Formula> substitution_list = new ArrayList<>();
        for (Formula formula: positive_formula_list) {
            Formula conceptF = TopConcept.getInstance();
            Formula conceptE = BottomConcept.getInstance();
            for (Formula subFormula: formula.getSubFormulas()) {
                if (subFormula.equals(concept)) { // C or A的形式
                    formula.getSubFormulas().remove(concept);
                    substitution_list.add(formula);
                    break;
                } else if (subFormula instanceof Leq) {
                    Formula filler = subFormula.getSubFormulas().get(1);
                    if (fChecker.negative(concept, filler) == 1) {
                        Leq leq = (Leq) subFormula;
                        if (leq.get_num() != 0) return null;
                        formula.getSubFormulas().remove(subFormula);
                        Formula conceptD = formula;
                        if (filler instanceof Or) {
                            for (Formula disjunct: filler.getSubFormulas()) {
                                if (fChecker.negative(concept, disjunct) == 1) {
                                    filler.getSubFormulas().remove(disjunct);
                                    conceptF = filler;
                                    if (disjunct instanceof And) {
                                        disjunct.getSubFormulas().remove(new Negation(concept));
                                        conceptE = disjunct;
                                    }
                                    break;
                                }
                            }
                        } else if (filler instanceof And) {
                            filler.getSubFormulas().remove(new Negation(concept));
                            conceptE = filler;
                        }
                        Formula tempFormula = new Leq(0, new InverseRole(subFormula.getSubFormulas().get(0)), new Negation(conceptD));
                        substitution_list.add(new Negation(new Or(conceptF, tempFormula)));
                        temp_output_list.add(new Or(tempFormula, new Negation(conceptE), new Negation(conceptF)));
                        break;
                    }
                }
            }

        }
        output_list.addAll(temp_output_list);
        return new Or(substitution_list);
    }

    private Formula getPositiveSubstitution(AtomicConcept concept, List<Formula> negative_formula_list, List<Formula> output_list) {
        FChecker fChecker = new FChecker();
        List<Formula> temp_output_list = new ArrayList<>();
        List<Formula> substitution_list = new ArrayList<>();
        for (Formula formula: negative_formula_list) {
            for (Formula subFormula: formula.getSubFormulas()) {
                if (subFormula.equals(new Negation(concept))) { // C or not A的形式
                    formula.getSubFormulas().remove(new Negation(concept));
                    substitution_list.add(formula);
                    break;
                } else if (subFormula instanceof Leq) {
                    Formula filler = subFormula.getSubFormulas().get(1);
                    if (fChecker.positive(concept, filler) == 1) {
                        Leq leq = (Leq) subFormula;
                        if (leq.get_num() != 0) return null;
                        Formula conceptF = TopConcept.getInstance();
                        Formula conceptE = BottomConcept.getInstance();
                        formula.getSubFormulas().remove(subFormula);
                        Formula conceptD = formula;
                        if (filler instanceof Or) {
                            for (Formula disjunct: filler.getSubFormulas()) {
                                if (fChecker.positive(concept, disjunct) == 1) {
                                    filler.getSubFormulas().remove(disjunct);
                                    conceptF = filler;
                                    if (disjunct instanceof And) {
                                        disjunct.getSubFormulas().remove(concept);
                                        conceptE = disjunct;
                                    }
                                    break;
                                }
                            }
                        } else if (filler instanceof And) {
                            filler.getSubFormulas().remove(concept);
                            conceptE = filler;
                        }
                        Formula tempFormula = new Leq(0, new InverseRole(subFormula.getSubFormulas().get(0)), new Negation(conceptD));
                        substitution_list.add(new Negation(new Or(conceptF, tempFormula)));
                        temp_output_list.add(new Or(tempFormula, new Negation(conceptE), new Negation(conceptF)));
                    }
                }
            }
        }
        output_list.addAll(temp_output_list);
        return new And(substitution_list);

    }

    private List<Formula> ackermannReplace(AtomicConcept concept, List<Formula> formula_list, Formula substitution) {
        List<Formula> output_list = new ArrayList<>();
        for (Formula formula: formula_list) {
            output_list.add(ackermannReplace(concept, formula, substitution));
        }
        return output_list;
    }

    private Formula ackermannReplace(AtomicConcept concept, Formula formula, Formula substitution) {
        if (formula instanceof AtomicConcept) {
            if (formula.equals(concept)) {
                return substitution;
            } else {
                return formula;
            }
        } else if (formula instanceof Negation) {
            return new Negation(ackermannReplace(concept, formula.getSubFormulas().get(0), substitution));
        } else if (formula instanceof Geq) {
            Geq geq = (Geq) formula;
            return new Geq(geq.get_num(), formula.getSubFormulas().get(0), ackermannReplace(concept, formula.getSubFormulas().get(1), substitution));
        } else if (formula instanceof Leq) {
            Leq leq = (Leq) formula;
            return new Leq(leq.get_num(), formula.getSubFormulas().get(0), ackermannReplace(concept, formula.getSubFormulas().get(1), substitution));
        } else if (formula instanceof And) {
            List<Formula> conjunct_list = formula.getSubFormulas();
            List<Formula> new_conjunct_list = new ArrayList<>();
            for (Formula conjunct: conjunct_list) {
                new_conjunct_list.add(ackermannReplace(concept, conjunct, substitution));
            }
            return new And(new_conjunct_list);
        } else if (formula instanceof Or) {
            List<Formula> disjunct_list = formula.getSubFormulas();
            List<Formula> new_disjunct_list = new ArrayList<>();
            for (Formula disjunct: disjunct_list) {
                new_disjunct_list.add(ackermannReplace(concept, disjunct, substitution));
            }
            return new Or(new_disjunct_list);
        } else {
            return formula;
        }
        }

}
