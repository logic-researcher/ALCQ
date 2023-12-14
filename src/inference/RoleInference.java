package inference;

import checkfrequency.FChecker;
import connectives.*;
import formula.Formula;
import roles.AtomicRole;
import roles.TopRole;

import java.util.ArrayList;
import java.util.List;


public class RoleInference {
    public List<Formula> forgettingRole(AtomicRole role, List<Formula> formulaList) throws CloneNotSupportedException {
        List<Formula> positiveList = new ArrayList<>();
        List<Formula> negativeList = new ArrayList<>();
        List<Formula> conceptExpList = new ArrayList<>();
        List<Formula> roleRestrictionList = new ArrayList<>();
        List<Integer> numRestrictionList = new ArrayList<>();
        List<Formula> conceptExpListNeg = new ArrayList<>();
        List<Formula> roleRestrictionListNeg = new ArrayList<>();
        List<Integer> numRestrictionListNeg = new ArrayList<>();
        separateFormulaList(role, formulaList, positiveList, negativeList);
        splitFormula(role, positiveList, conceptExpList, roleRestrictionList, numRestrictionList);
        splitFormula(role, negativeList, conceptExpListNeg, roleRestrictionListNeg, numRestrictionListNeg);
        List<Formula> outputList = new ArrayList<>(groundTier(conceptExpList, roleRestrictionList));
        for (int i = 0; i < conceptExpListNeg.size(); i++) {
            List<Formula> combinedList = combinePositiveNegative(conceptExpListNeg.get(i), (Leq)roleRestrictionListNeg.get(i), conceptExpList, roleRestrictionList, numRestrictionList);
            outputList.addAll(combinedList);
        }

        return outputList;
    }
    
    private void separateFormulaList(AtomicRole role, List<Formula> formulaList, List<Formula> positiveList, List<Formula> negativeList) {
        FChecker fChecker = new FChecker();
        for (Formula formula : formulaList) {
            if (fChecker.positive(role, formula) == 1) {
                positiveList.add(formula);
            } else if (fChecker.negative(role, formula) == 1) {
                negativeList.add(formula);
            }
        }
    }

    private void splitFormula(AtomicRole role, List<Formula> formulaList, List<Formula> conceptExpList, List<Formula> roleRestrictionList, List<Integer> numRestrictionList) {
        FChecker fChecker = new FChecker();
        for (Formula formula: formulaList) {
            for (Formula subConcept: formula.getSubFormulas()) {
                if ((subConcept instanceof Geq && fChecker.positive(role, subConcept) == 1)
                        || (subConcept instanceof Leq && fChecker.negative(role, subConcept) == 1)) {
                    subConcept.getSubFormulas().remove(0);
                    subConcept.getSubFormulas().add(0, new TopRole());
                    roleRestrictionList.add(subConcept);
                    formula.getSubFormulas().remove(subConcept);
                    conceptExpList.add(formula);
                    if (subConcept instanceof Geq) {
                        numRestrictionList.add(((Geq) subConcept).get_num());
                    } else {
                        numRestrictionList.add(((Leq) subConcept).get_num());
                    }
                    break;
                }
            }
        }
        assert conceptExpList.size() == roleRestrictionList.size();
    }

    private List<Formula> combinePositiveNegative(Formula conceptExp, Leq numRestrict, List<Formula> conceptExpList, List<Formula> roleRestrictionList, List<Integer> numRestrictionList) {
        List<Formula> outputList = new ArrayList<>();
        int m = conceptExpList.size();
        List<Integer> nums1 = new ArrayList<>();
        for (int i = 0; i < m; i++) {
            nums1.add(i);
        }
        for (int k = 1; k <= m; k++) {
            List<List<Integer>> combinations = generateSubsets(nums1, k);
            for(List<Integer> combination: combinations) {
                int lastNumRestriction = -numRestrict.get_num();

                Or conceptExpOr = new Or(conceptExp);
                List<Formula> fillerList = new ArrayList<>();
                for (Integer i: combination) {
                    lastNumRestriction += numRestrictionList.get(i);
                    conceptExpOr.getSubFormulas().add(conceptExpList.get(i));
                    fillerList.add(roleRestrictionList.get(i).getSubFormulas().get(1));
                }
                for (int j = 2; j <= k; j++) {
                    List<List<Integer>> combinations2 = generateSubsets(combination, j);
                    if (j % 2 == 0) {
                        for (List<Integer> combination2: combinations2) {
                            int y = 0;
                            List<Formula> fillerList2 = new ArrayList<>();
                            for (int idx : combination2) {
                                y = Math.max(y, numRestrictionList.get(idx));
                                fillerList2.add(roleRestrictionList.get(idx).getSubFormulas().get(1));
                            }
                            And filler = new And(fillerList2);

                            Geq geq = new Geq(y + 1, TopRole.getInstance(), filler);
                            conceptExpOr.getSubFormulas().add(geq);
                            lastNumRestriction += (1 - y);
                        }
                    } else {
                        for (List<Integer> combination2: combinations2) {
                            int y = 999;
                            List<Formula> fillerList3 = new ArrayList<>();
                            for (int idx : combination2) {
                                y = Math.min(y, numRestrictionList.get(idx));
                                fillerList3.add(roleRestrictionList.get(idx).getSubFormulas().get(1));
                            }
                            And filler = new And(fillerList3);

                            if (y >= 1) {
                                Leq leq = new Leq(y - 1, TopRole.getInstance(), filler);
                                conceptExpOr.getSubFormulas().add(leq);
                                lastNumRestriction += (1 + y);
                            }
                        }
                    }
                }
                Or filler = new Or(fillerList);
               And andFiller = new And(filler);
               andFiller.getSubFormulas().add(new Negation(numRestrict.getSubFormulas().get(1)));
               conceptExpOr.getSubFormulas().add(new Geq(lastNumRestriction, TopRole.getInstance(), andFiller));
                outputList.add(conceptExpOr);

            }

        }
        return outputList;
    }

    private List<Formula> groundTier(List<Formula> conceptExpList, List<Formula> numRestrictionList) throws CloneNotSupportedException {
        List<Formula> outputList = new ArrayList<>();
        for (int i = 0; i < conceptExpList.size(); i++) {
            Formula conceptExp = conceptExpList.get(i).clone();
            Formula numRestrict = numRestrictionList.get(i).clone();
            conceptExp.getSubFormulas().add(numRestrict);
            outputList.add(conceptExp);
        }
        return outputList;
    }

    public static List<List<Integer>> generateSubsets(List<Integer> nums, int k) {
        List<List<Integer>> result = new ArrayList<>();
        generateSubsetsHelper(nums, k, 0, new ArrayList<>(), result);
        return result;
    }

    private static void generateSubsetsHelper(List<Integer> nums, int k, int start, List<Integer> current, List<List<Integer>> result) {
        if (current.size() == k) {
            result.add(new ArrayList<>(current));
            return;
        }

        for (int i = start; i < nums.size(); i++) {
            current.add(nums.get(i));
            generateSubsetsHelper(nums, k, i + 1, current, result);
            current.remove(current.size() - 1);
        }
    }
}
