package inference;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

//import com.sun.source.tree.NewArrayTree;
import convertion.Converter;
import extraction.SubsetExtractor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Geq;
import connectives.Leq;
import connectives.Negation;
import connectives.Or;
import convertion.BackConverter;
import formula.Formula;
import roles.AtomicRole;
import simplification.Simplifier;
import inference.Inferencer;
import Exception.CyclicCaseException;

public class DefinerIntroducer {



	public DefinerIntroducer() {

	}

	public static Map<Formula, AtomicConcept> definer_map = new HashMap<>();
	public static Map<Formula, Integer> definer_flag_map = new HashMap<>(); //flag=1~neg_define or A;flag=2~neg_A or define;flag=3~all in
	public static Set<OWLEntity> owldefiner_set = new HashSet<>();
	public static Set<AtomicConcept> definer_set = new HashSet<>();
	public static Set<AtomicConcept> cyclic_definer_set = new HashSet<>();
	public static List<Formula> reuse_formula = new ArrayList<>();
	public static Map<AtomicConcept, Formula> Cyclic_map = new HashMap<>();


	public List<Formula> introduceDefiners(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException, CyclicCaseException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(concept, formula));
		}
		//System.out.println(output_list);
		return output_list;
	}

	/*private List<Formula> introduceDefiners(AtomicConcept concept, Formula formula) throws CloneNotSupportedException {
		
		BackConverter bc = new BackConverter();
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		Simplifier pp = new Simplifier();

		List<Formula> output_list = new ArrayList<>();

		if (fc.positive(concept, formula) + fc.negative(concept, formula) == 1) {

			if (formula instanceof Exists || formula instanceof Forall) {

				Formula filler = formula.getSubFormulas().get(1);

				if (filler.equals(concept) || filler.equals(new Negation(concept))) {

					output_list.add(formula);

				} else if (filler instanceof Or && (filler.getSubFormulas().contains(concept)
						|| filler.getSubFormulas().contains(new Negation(concept)))) {

					output_list.add(formula);

				} else {

					if (definer_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}

					} else {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();
				// System.out.println("disjuncts = " + disjuncts);
				if (disjuncts.contains(concept) || disjuncts.contains(new Negation(concept))) {
					output_list.add(formula);

				} else {

					for (Formula disjunct : disjuncts) {
						if (ec.isPresent(concept, disjunct)) {
							// do we really need this step? cause can only be Exists or Forall
							// if (disjunct instanceof Exists || disjunct instanceof Forall) {

							Formula filler = disjunct.getSubFormulas().get(1);

							if (filler.equals(concept) || filler.equals(new Negation(concept))) {
								output_list.add(formula);
								break;

							} else if (filler instanceof Or && (filler.getSubFormulas().contains(concept)
									|| filler.getSubFormulas().contains(new Negation(concept)))) {
								output_list.add(formula);
								break;

							} else {

								if (definer_map.get(filler) == null) {
									AtomicConcept definer = new AtomicConcept(
											"Definer_" + AtomicConcept.getDefiner_index());
									AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
									definer_set.add(definer);
									owldefiner_set.add(bc.getClassfromConcept(definer));
									definer_map.put(filler, definer);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(new Negation(definer));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										// System.out.println("disjunct_list = " + disjunct_list);
										output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
									}
									break;

								} else {
									AtomicConcept definer = definer_map.get(filler);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
									break;
								}
							}
							// }
						}
					}
				}

			} else {
				// none of the cases of Exists, Forall, Or
				output_list.add(formula);
			}

		} else if (fc.positive(concept, formula) + fc.negative(concept, formula) > 1) {

			if (formula instanceof Exists || formula instanceof Forall) {

				Formula filler = formula.getSubFormulas().get(1);

				if (definer_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_map.put(filler, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					List<Formula> conjunct_list = null;
					if (filler instanceof And) {
						conjunct_list = filler.getSubFormulas();
					} else {
						conjunct_list = pp.getCNF(filler);
					}
					for (Formula conjunct : conjunct_list) {
						List<Formula> disjunct_list = new ArrayList<>();
						disjunct_list.add(new Negation(definer));
						if (conjunct instanceof Or) {
							disjunct_list.addAll(conjunct.getSubFormulas());
						} else {
							disjunct_list.add(conjunct);
						}
						output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
					}

				} else {
					AtomicConcept definer = definer_map.get(filler);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();

				for (int i = 0; i < disjuncts.size(); i++) {
					Formula disjunct = disjuncts.get(i);
					// unsure about this: && (disjunct instanceof Exists || disjunct instanceof
					// Forall)
					if (ec.isPresent(concept, disjunct)) {
						if ((fc.positive(concept, formula) + fc.negative(concept, formula))
								- (fc.positive(concept, disjunct) + fc.negative(concept, disjunct)) > 0) {

							if (definer_map.get(disjunct) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(disjunct, definer);
								disjuncts.set(i, definer);
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								disjunct_list.add(disjunct);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
								break;

							} else {
								AtomicConcept definer = definer_map.get(disjunct);
								disjuncts.set(i, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}

						} else {
							Formula filler = disjunct.getSubFormulas().get(1);

							if (definer_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(filler, definer);
								disjuncts.get(i).getSubFormulas().set(1, definer);
								output_list.add(formula);
								// List<Formula> conjunct_list =
								// pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler)));
								// List<Formula> conjunct_list = pp.getCNF(filler);
								List<Formula> conjunct_list = null;
								if (filler instanceof And) {
									conjunct_list = filler.getSubFormulas();
								} else {
									conjunct_list = pp.getCNF(filler);
								}
								for (Formula conjunct : conjunct_list) {
									List<Formula> disjunct_list = new ArrayList<>();
									disjunct_list.add(new Negation(definer));
									if (conjunct instanceof Or) {
										disjunct_list.addAll(conjunct.getSubFormulas());
									} else {
										disjunct_list.add(conjunct);
									}
									output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
								}
								break;

							} else {
								AtomicConcept definer = definer_map.get(filler);
								disjuncts.get(i).getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
						}
					}
				}

			} else {
				output_list.add(formula);
			}

		} else {
			// do not contain A
			output_list.add(formula);
		}

		return output_list;
	}*/
	private List<Formula> introduceDefiners(AtomicConcept concept, Formula formula) throws CloneNotSupportedException, CyclicCaseException { //SQ

		BackConverter bc = new BackConverter();
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		Simplifier pp = new Simplifier();

		List<Formula> output_list = new ArrayList<>();

		if (fc.positive(concept, formula) + fc.negative(concept, formula) == 1) {

			if (formula instanceof Leq) {

				Formula filler = formula.getSubFormulas().get(1);

				if (isStandard(concept,filler)) {
					output_list.add(formula);

				}  else {

					if (definer_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						//System.out.println("intro"+definer);
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						definer_flag_map.put(definer, 2);
						Formula neg_filler = new Negation(filler);
						neg_filler = pp.removenegation(neg_filler);
						List<Formula> conjunct_list = null;

						if (neg_filler instanceof And) {
							conjunct_list = neg_filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(neg_filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(definer);
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}

					} else {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						if (definer_flag_map.get(definer) == 1) {
							definer_flag_map.remove(definer);
							definer_flag_map.put(definer, 3);
							Formula neg_filler = new Negation(filler);
							neg_filler = pp.removenegation(neg_filler);
							List<Formula> conjunct_list = null;
							if (neg_filler instanceof And) {
								conjunct_list = neg_filler.getSubFormulas();
							} else {
								conjunct_list = pp.getCNF(neg_filler);
							}
							for (Formula conjunct : conjunct_list) {
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(definer);
								if (conjunct instanceof Or) {
									disjunct_list.addAll(conjunct.getSubFormulas());
								} else {
									disjunct_list.add(conjunct);
								}
								output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
							}
						}
					}
				}
			} else if (formula instanceof Geq){
				Formula filler = formula.getSubFormulas().get(1);

				if (isStandard(concept,filler)) {

					output_list.add(formula);

				}  else {

					if (definer_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						//System.out.println("intro"+definer);
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						definer_flag_map.put(definer, 1);
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}
					} else {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						definer_flag_map.remove(definer);
						definer_flag_map.put(definer, 3);
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}
					}
				}


			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();
				// System.out.println("disjuncts = " + disjuncts);
				if (disjuncts.contains(concept) || disjuncts.contains(new Negation(concept))) {
					output_list.add(formula);

				} else {

					for (Formula disjunct : disjuncts) {
						if (ec.isPresent(concept, disjunct)) {

							formula.getSubFormulas().remove(disjunct);
							Formula filler = disjunct.getSubFormulas().get(1);

							if (isStandard(concept,filler)) {
								formula.getSubFormulas().add(disjunct);
								output_list.add(formula);
								break;

							} else {

								if (definer_map.get(filler) == null) {
									AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
									//System.out.println("intro"+definer);
									AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
									definer_set.add(definer);
									owldefiner_set.add(bc.getClassfromConcept(definer));
									definer_map.put(filler, definer);
									disjunct.getSubFormulas().set(1, definer);
									formula.getSubFormulas().add(disjunct);
									output_list.add(formula);
									if (disjunct instanceof Geq) {
										definer_flag_map.put(definer, 1);
										List<Formula> conjunct_list = null;
										if (filler instanceof And) {
											conjunct_list = filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(new Negation(definer));
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
										}

									} else {
										definer_flag_map.put(definer, 2);
										Formula neg_filler = new Negation(filler);
										neg_filler = pp.removenegation(neg_filler);
										List<Formula> conjunct_list = null;
										if (neg_filler instanceof And) {
											conjunct_list = neg_filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(neg_filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(definer);
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
										}

									}
									break;

								} else {
									AtomicConcept definer = definer_map.get(filler);
									disjunct.getSubFormulas().set(1, definer);
									formula.getSubFormulas().add(disjunct);
									output_list.add(formula);
									if (definer_flag_map.get(definer)==1 && disjunct instanceof Leq) {
										definer_flag_map.remove(definer);
										definer_flag_map.put(definer,3);
										Formula neg_filler = new Negation(filler);
										neg_filler = pp.removenegation(neg_filler);
										List<Formula> conjunct_list = null;
										if (neg_filler instanceof And) {
											conjunct_list = neg_filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(neg_filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(definer);
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
										}

									} else if(definer_flag_map.get(definer)==2 && disjunct instanceof Geq) {
										definer_flag_map.remove(definer);
										definer_flag_map.put(definer,3);
										List<Formula> conjunct_list = null;
										if (filler instanceof And) {
											conjunct_list = filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(new Negation(definer));
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
										}
									}
									break;
								}
							}
						}
					}
				}

			} else {
				// none of the cases of Geq, Leq, Or
				output_list.add(formula);
			}

		} else if (fc.positive(concept, formula) + fc.negative(concept, formula) > 1) {

			/*if (fc.positive(concept, formula)>=1 && fc.negative(concept, formula) >= 1){
				throw new CyclicCaseException(formula);
			}*/

			if (isCyclicCase(concept,formula)){
				throw new CyclicCaseException(formula);
			}
			if (formula instanceof Geq || formula instanceof Leq) {

				Formula filler = formula.getSubFormulas().get(1);

				if (definer_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
					//FSystem.out.println("intro"+definer);
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_map.put(filler, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					if (formula instanceof Geq) {
						definer_flag_map.put(definer, 1);
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}

					} else {
						definer_flag_map.put(definer, 2);
						Formula neg_filler = new Negation(filler);
						neg_filler = pp.removenegation(neg_filler);
						List<Formula> conjunct_list = null;
						if (neg_filler instanceof And) {
							conjunct_list = neg_filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(neg_filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(definer);
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}

					}

				} else {
					AtomicConcept definer = definer_map.get(filler);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					if (definer_flag_map.get(definer)==1 && formula instanceof Leq) {
						definer_flag_map.remove(definer);
						definer_flag_map.put(definer,3);
						Formula neg_filler = new Negation(filler);
						neg_filler = pp.removenegation(neg_filler);
						List<Formula> conjunct_list = null;
						if (neg_filler instanceof And) {
							conjunct_list = neg_filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(neg_filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(definer);
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}

					} else if(definer_flag_map.get(definer)==2 && formula instanceof Geq) {
						definer_flag_map.remove(definer);
						definer_flag_map.put(definer,3);
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}
					}
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();

				for (int i = 0; i < disjuncts.size(); i++) {
					Formula disjunct = disjuncts.get(i);
					if (ec.isPresent(concept, disjunct)) {
						if ((fc.positive(concept, formula) + fc.negative(concept, formula))
								- (fc.positive(concept, disjunct) + fc.negative(concept, disjunct)) > 0) {

							if (definer_map.get(disjunct) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								//System.out.println("intro"+definer);
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(disjunct, definer);
								definer_flag_map.put(definer, 1);
								formula.getSubFormulas().set(i, definer);
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								disjunct_list.add(disjunct);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
								break;

							} else {
								AtomicConcept definer = definer_map.get(disjunct);
								formula.getSubFormulas().set(i, definer);
								if (definer_flag_map.get(definer)==2) {
									definer_flag_map.remove(definer);
									definer_flag_map.put(definer, 3);
									List<Formula> disjunct_list = new ArrayList<>();
									disjunct_list.add(new Negation(definer));
									disjunct_list.add(disjunct);
									output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
								}
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}

						} else {
							formula.getSubFormulas().remove(disjunct);
							Formula filler = disjunct.getSubFormulas().get(1);

							if (definer_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
								//System.out.println("intro"+definer);
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(filler, definer);
								disjunct.getSubFormulas().set(1, definer);
								formula.getSubFormulas().add(disjunct);
								output_list.add(formula);
								if (disjunct instanceof Geq) {
									definer_flag_map.put(definer, 1);
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(new Negation(definer));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
									}

								} else {
									definer_flag_map.put(definer, 2);
									Formula neg_filler = new Negation(filler);
									neg_filler = pp.removenegation(neg_filler);
									List<Formula> conjunct_list = null;
									if (neg_filler instanceof And) {
										conjunct_list = neg_filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(neg_filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(definer);
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
									}

								}
								break;

							} else {
								AtomicConcept definer = definer_map.get(filler);
								disjunct.getSubFormulas().set(1, definer);
								formula.getSubFormulas().add(disjunct);
								output_list.add(formula);
								if (definer_flag_map.get(definer)==1 && disjunct instanceof Leq) {
									definer_flag_map.remove(definer);
									definer_flag_map.put(definer,3);
									Formula neg_filler = new Negation(filler);
									neg_filler = pp.removenegation(neg_filler);
									List<Formula> conjunct_list = null;
									if (neg_filler instanceof And) {
										conjunct_list = neg_filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(neg_filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(definer);
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
									}

								} else if(definer_flag_map.get(definer)==2 && disjunct instanceof Geq) {
									definer_flag_map.remove(definer);
									definer_flag_map.put(definer,3);
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(new Negation(definer));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
									}
								}
								break;
							}
						}
					}
				}

			} else {
				output_list.add(formula);
			}

		} else {
			// do not contain A
			output_list.add(formula);
		}

		return output_list;
	}


	public List<Formula> introduceDefiners(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(role, formula));
		}

		return output_list;
	}

	private List<Formula> introduceDefiners(AtomicRole role, Formula formula) throws CloneNotSupportedException{ // for SHQ
		OWLOntologyManager man = OWLManager.createOWLOntologyManager();

		BackConverter bc = new BackConverter();
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		Simplifier pp = new Simplifier();

		List<Formula> output_list = new ArrayList<>();

		if (fc.positive(role, formula) + fc.negative(role, formula) == 1) {

			if (formula instanceof Leq || formula instanceof Geq) {
				Formula formula_role = formula.getSubFormulas().get(0);
				Formula filler = formula.getSubFormulas().get(1);
				if (formula_role.equals(role)) {
					output_list.add(formula);

				} else {
					if (definer_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						man.addAxiom(Converter.ontology,bc.toOWLAxiom(bc.toInclusion(formula)));
						output_list.add(formula);
						if (formula instanceof Geq) {
							definer_flag_map.put(definer, 1);
							List<Formula> conjunct_list = null;
							if (filler instanceof And) {
								conjunct_list = filler.getSubFormulas();
							} else {
								conjunct_list = pp.getCNF(filler);
							}
							for (Formula conjunct : conjunct_list) {
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								if (conjunct instanceof Or) {
									disjunct_list.addAll(conjunct.getSubFormulas());
								} else {
									disjunct_list.add(conjunct);
								}
								output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
								man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
							}
							
						} else {
							definer_flag_map.put(definer, 2);
							Formula neg_filler = new Negation(filler);
							neg_filler = pp.removenegation(neg_filler);
							List<Formula> conjunct_list = null;
							if (neg_filler instanceof And) {
								conjunct_list = neg_filler.getSubFormulas();
							} else {
								conjunct_list = pp.getCNF(neg_filler);
							}
							for (Formula conjunct : conjunct_list) {
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(definer);
								if (conjunct instanceof Or) {
									disjunct_list.addAll(conjunct.getSubFormulas());
								} else {
									disjunct_list.add(conjunct);
								}
								output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
								man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
							}
							
						}

					} else {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						man.addAxiom(Converter.ontology,bc.toOWLAxiom(bc.toInclusion(formula)));
						if (definer_flag_map.get(definer)==1 && formula instanceof Leq) {
							definer_flag_map.remove(definer);
							definer_flag_map.put(definer,3);
							Formula neg_filler = new Negation(filler);
							neg_filler = pp.removenegation(neg_filler);
							List<Formula> conjunct_list = null;
							if (neg_filler instanceof And) {
								conjunct_list = neg_filler.getSubFormulas();
							} else {
								conjunct_list = pp.getCNF(neg_filler);
							}
							for (Formula conjunct : conjunct_list) {
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(definer);
								if (conjunct instanceof Or) {
									disjunct_list.addAll(conjunct.getSubFormulas());
								} else {
									disjunct_list.add(conjunct);
								}
								output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
								man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
							}
							
						} else if(definer_flag_map.get(definer)==2 && formula instanceof Geq) {
							definer_flag_map.remove(definer);
							definer_flag_map.put(definer,3);
							List<Formula> conjunct_list = null;
							if (filler instanceof And) {
								conjunct_list = filler.getSubFormulas();
							} else {
								conjunct_list = pp.getCNF(filler);
							}
							for (Formula conjunct : conjunct_list) {
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								if (conjunct instanceof Or) {
									disjunct_list.addAll(conjunct.getSubFormulas());
								} else {
									disjunct_list.add(conjunct);
								}
								output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
								man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
							}
						}
					}
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();

				if (disjuncts.contains(role) || disjuncts.contains(new Negation(role))) {
					output_list.add(formula);

				} else {
					for (Formula disjunct : disjuncts) {
						if (ec.isPresent(role, disjunct)) {
							Formula disjunct_role = disjunct.getSubFormulas().get(0);
							if (disjunct_role.equals(role)) {
								output_list.add(formula);
								break;

							} else {
								formula.getSubFormulas().remove(disjunct);
								Formula filler = disjunct.getSubFormulas().get(1);

								if (definer_map.get(filler) == null) {
									AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
									AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
									definer_set.add(definer);
									owldefiner_set.add(bc.getClassfromConcept(definer));
									definer_map.put(filler, definer);
									disjunct.getSubFormulas().set(1, definer);
									formula.getSubFormulas().add(disjunct);
									output_list.add(formula);
									man.addAxiom(Converter.ontology,bc.toOWLAxiom(bc.toInclusion(formula)));
									if (disjunct instanceof Geq) {
										definer_flag_map.put(definer, 1);
										List<Formula> conjunct_list = null;
										if (filler instanceof And) {
											conjunct_list = filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(new Negation(definer));
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
											man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
										}
										
									} else {
										definer_flag_map.put(definer, 2);
										Formula neg_filler = new Negation(filler);
										neg_filler = pp.removenegation(neg_filler);
										List<Formula> conjunct_list = null;
										if (neg_filler instanceof And) {
											conjunct_list = neg_filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(neg_filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(definer);
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
											man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
										}
										
									}
									break;

								} else {
									AtomicConcept definer = definer_map.get(filler);
									disjunct.getSubFormulas().set(1, definer);
									formula.getSubFormulas().add(disjunct);
									output_list.add(formula);
									if (definer_flag_map.get(definer)==1 && disjunct instanceof Leq) {
										definer_flag_map.remove(definer);
										definer_flag_map.put(definer,3);
										Formula neg_filler = new Negation(filler);
										neg_filler = pp.removenegation(neg_filler);
										List<Formula> conjunct_list = null;
										if (neg_filler instanceof And) {
											conjunct_list = neg_filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(neg_filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(definer);
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
											man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
										}
										
									} else if(definer_flag_map.get(definer)==2 && disjunct instanceof Geq) {
										definer_flag_map.remove(definer);
										definer_flag_map.put(definer,3);
										List<Formula> conjunct_list = null;
										if (filler instanceof And) {
											conjunct_list = filler.getSubFormulas();
										} else {
											conjunct_list = pp.getCNF(filler);
										}
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(new Negation(definer));
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
											man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
										}
									}
									break;
								}
							}
						}
					}
				}
			}

		} else if (fc.positive(role, formula) + fc.negative(role, formula) > 1) {

			if (formula instanceof Leq || formula instanceof Geq) {
				Formula filler = formula.getSubFormulas().get(1);

				if (definer_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_map.put(filler, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					if (formula instanceof Geq) {
						definer_flag_map.put(definer, 1);
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
							man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
						}
						
					} else {
						definer_flag_map.put(definer, 2);
						Formula neg_filler = new Negation(filler);
						neg_filler = pp.removenegation(neg_filler);
						List<Formula> conjunct_list = null;
						if (neg_filler instanceof And) {
							conjunct_list = neg_filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(neg_filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(definer);
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
							man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
						}
						
					}

				} else {
					AtomicConcept definer = definer_map.get(filler);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					if (definer_flag_map.get(definer)==1 && formula instanceof Leq) {
						definer_flag_map.remove(definer);
						definer_flag_map.put(definer,3);
						Formula neg_filler = new Negation(filler);
						neg_filler = pp.removenegation(neg_filler);
						List<Formula> conjunct_list = null;
						if (neg_filler instanceof And) {
							conjunct_list = neg_filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(neg_filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(definer);
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
							man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
						}
						
					} else if(definer_flag_map.get(definer)==2 && formula instanceof Geq) {
						definer_flag_map.remove(definer);
						definer_flag_map.put(definer,3);
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);
							}
							output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
							man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
						}
					}
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();

				for (int i = 0; i < disjuncts.size(); i++) {
					Formula disjunct = disjuncts.get(i);

					if (ec.isPresent(role, disjunct)) {
						if ((fc.positive(role, formula) + fc.negative(role, formula))
								- (fc.positive(role, disjunct) + fc.negative(role, disjunct)) > 0) {

							if (definer_map.get(disjunct) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(disjunct, definer);
								definer_flag_map.put(definer, 1);
								formula.getSubFormulas().set(i, definer);
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								disjunct_list.add(disjunct);
								output_list.addAll(introduceDefiners(role, formula));
								output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
								man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
								break;

							} else {
								AtomicConcept definer = definer_map.get(disjunct);
								formula.getSubFormulas().set(i, definer);
								if (definer_flag_map.get(definer)==2) {
									definer_flag_map.remove(definer);
									definer_flag_map.put(definer, 3);
									List<Formula> disjunct_list = new ArrayList<>();
									disjunct_list.add(new Negation(definer));
									disjunct_list.add(disjunct);
									output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
									man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
								}
								output_list.addAll(introduceDefiners(role, formula));
								break;
							}

						} else {

							formula.getSubFormulas().remove(disjunct);
							Formula filler = disjunct.getSubFormulas().get(1);

							if (definer_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(filler, definer);
								disjunct.getSubFormulas().set(1, definer);
								formula.getSubFormulas().add(disjunct);
								output_list.add(formula);
								if (disjunct instanceof Geq) {
									definer_flag_map.put(definer, 1);
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(new Negation(definer));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
										man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
									}
									
								} else {
									definer_flag_map.put(definer, 2);
									Formula neg_filler = new Negation(filler);
									neg_filler = pp.removenegation(neg_filler);
									List<Formula> conjunct_list = null;
									if (neg_filler instanceof And) {
										conjunct_list = neg_filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(neg_filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(definer);
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
										man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
									}
									
								}
								break;

							} else {
								AtomicConcept definer = definer_map.get(filler);
								disjunct.getSubFormulas().set(1, definer);
								formula.getSubFormulas().add(disjunct);
								output_list.add(formula);
								if (definer_flag_map.get(definer)==1 && disjunct instanceof Leq) {
									definer_flag_map.remove(definer);
									definer_flag_map.put(definer,3);
									Formula neg_filler = new Negation(filler);
									neg_filler = pp.removenegation(neg_filler);
									List<Formula> conjunct_list = null;
									if (neg_filler instanceof And) {
										conjunct_list = neg_filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(neg_filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(definer);
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
										man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
									}
									
								} else if(definer_flag_map.get(definer)==2 && disjunct instanceof Geq) {
									definer_flag_map.remove(definer);
									definer_flag_map.put(definer,3);
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(new Negation(definer));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
										man.addAxioms(Converter.ontology,bc.toOWLAxioms(introduceDefiners(role, new Or(disjunct_list))));
									}
								}
								break;
							}
						}
					}
				}

			} else {
				output_list.add(formula);
			}

		} else {
			output_list.add(formula);
		}
		// System.out.println("output_list = " + output_list);
		return output_list;
	}


	public List<Formula> Intro_Cyclic_Definers(AtomicConcept concept, List<Formula> input_list){
		EChecker ec = new EChecker();
		SubsetExtractor se = new SubsetExtractor();
		List<Formula> output_list = new ArrayList<>();
		for(Formula formula : input_list){
			output_list.add(formula);
			if (ec.isPresent(concept,formula)) {
				//if (formula instanceof Leq && Converter.TransitiveRole_Set.contains(formula.getSubFormulas().get(0))) {
				if (formula instanceof Leq){
					Set<AtomicRole> subtransrole = getSubTransRoles((AtomicRole) formula.getSubFormulas().get(0));
					for (AtomicRole role : subtransrole) {
						AtomicConcept Cycdefiner = new AtomicConcept("Definer_Cyc_" + AtomicConcept.getCyclic_definer_index());
						AtomicConcept.setCyclic_definer_index(AtomicConcept.getCyclic_definer_index() + 1);
						Formula reuse1 = new Leq(0, role, new Negation(Cycdefiner));
						cyclic_definer_set.addAll(se.getDefinersFromFormula(reuse1));
						List<Formula> or_list = new ArrayList<>();
						or_list.add(new Negation(Cycdefiner));
						or_list.add(new Leq(0, role, new Negation(Cycdefiner)));
						Formula reuse2 = new Or(or_list);
						Cyclic_map.put(Cycdefiner, reuse2);
						or_list.clear();
						or_list.add(new Negation(Cycdefiner));
						or_list.add(formula);
						Formula use3 = new Or(or_list);

						output_list.add(reuse1);
						output_list.add(use3);
						reuse_formula.add(reuse1);
					}



				} else if (formula instanceof Or){
					List<Formula> disjunct_list = new ArrayList<>(formula.getSubFormulas());
					for (Formula disjunct : disjunct_list){
						if(ec.isPresent(concept,disjunct)){
							if (disjunct instanceof Leq) {
								Set<AtomicRole> subtransrole = getSubTransRoles((AtomicRole) disjunct.getSubFormulas().get(0));
								for (AtomicRole role : subtransrole) {
									AtomicConcept Cycdefiner = new AtomicConcept("Definer_Cyc_" + AtomicConcept.getCyclic_definer_index());
									AtomicConcept.setCyclic_definer_index(AtomicConcept.getCyclic_definer_index() + 1);
									List<Formula> or_list = new ArrayList<>(disjunct_list);
									or_list.remove(disjunct);
									or_list.add(new Leq(0, role, new Negation(Cycdefiner)));
									Formula reuse1 = new Or(or_list);
									cyclic_definer_set.addAll(se.getDefinersFromFormula(reuse1));
									or_list.clear();
									or_list.add(new Negation(Cycdefiner));
									or_list.add(new Leq(0, role, new Negation(Cycdefiner)));
									Formula reuse2 = new Or(or_list);
									Cyclic_map.put(Cycdefiner, reuse2);
									or_list.clear();
									or_list.add(new Negation(Cycdefiner));
									or_list.add(disjunct);
									Formula use3 = new Or(or_list);

									output_list.add(reuse1);
									output_list.add(use3);
									reuse_formula.add(reuse1);
								}
								break;
							} else {
								break;
							}
						}

					}
				} else {
					continue;
				}
			}
		}
		return output_list;
	}

	public static void reset(){
		definer_map.clear();
		definer_flag_map.clear();
		owldefiner_set.clear();
		definer_set.clear();
		cyclic_definer_set.clear();
		reuse_formula.clear();
		Cyclic_map.clear();
		AtomicConcept.update_total_index();
		AtomicConcept.setDefiner_index(1);
		AtomicConcept.setCyclic_definer_index(1);
	}

	public static boolean isStandard(AtomicConcept concept, Formula formula){
		EChecker ec = new EChecker();
		if (formula.equals(concept) || formula.equals(new Negation(concept))){
			return true;
		} else if (formula instanceof And && (formula.getSubFormulas().contains(concept) ||
				formula.getSubFormulas().contains(new Negation(concept)))){
			return true;
		} else if (formula instanceof Or){
			if (formula.getSubFormulas().contains(concept) || formula.getSubFormulas().contains(new Negation(concept))){
				return true;
			} else {
				for (Formula disjunct : formula.getSubFormulas()){
					if (ec.isPresent(concept,disjunct) && disjunct instanceof And &&
							(disjunct.getSubFormulas().contains(concept) || disjunct.getSubFormulas().contains(new Negation(concept)))){
						return true;
					}
				}
				return false;
			}
		} else {
			return false;
		}
	}


	public static Set<AtomicRole> getSubTransRoles(AtomicRole role){
		Set<AtomicRole> subrolelist = new HashSet<>();
		for (AtomicRole srole : Inferencer.getsubRoles(role,new HashSet<>())){
			System.out.println(srole);
			if (Converter.TransitiveRole_Set.contains(srole)){
				subrolelist.add(srole);
			}
		}
		if (Converter.TransitiveRole_Set.contains(role)){
			subrolelist.add(role);
		}
		return subrolelist;
	}

	public boolean isCyclicCase(AtomicConcept concept, Formula formula){
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		if(fc.positive(concept,formula)>=1 && fc.negative(concept, formula)>=1){
			if (formula instanceof Or){
				if(formula.getSubFormulas().contains(concept) || formula.getSubFormulas().contains(new Negation(concept))){
					return true;
				}
			}
		}
		return false;
	}



}
