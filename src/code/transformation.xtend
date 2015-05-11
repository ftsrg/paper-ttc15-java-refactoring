/**
 * This class implements the transformation logic.
 */
class Transformation {

	/**
	 * Initialize the transformation processor on a resource.
	 * The runtime of the transformation steps are logged.
	 * @param r The target resource of the transformation.
	 * @param bmr The benchmark logger.
	 */
	new (Resource r, BenchmarkResults bmr) {
		this.r = r;
		this.bmr = bmr;
		this.root = r.contents.get(0) as Root
	}
	
	// to store the benchmark results
	protected val BenchmarkResults bmr;
	// to store the model
	protected Resource r
	
	////// Resources Management
	protected val Root root;
	/**
	 * Helper function to add elements to the target resource.
	 * @param
	 */
	def addElementToResource(ContainedElement containedElement) {
		root.children.add(containedElement)
	}
	def addElementsToResource(Collection<? extends ContainedElement> containedElements) {
		root.children.addAll(containedElements)
	}
	def getElementsFromResource() {
		root.children
	}
	////////////////////////////
	
	// to help with model manipulation
	extension MoviesFactory = MoviesFactory.eINSTANCE
	extension Imdb = Imdb.instance

	// create couples
	public def createCouples() { (*@\label{xform:createCouples}@*)
		val engine = AdvancedIncQueryEngine.createUnmanagedEngine(r)
		val coupleMatcher = engine.personsToCouple
		val commonMoviesMatcher = engine.commonMoviesToCouple
		val personNameMatcher = engine.personName
		
		val newCouples = new LinkedList<Couple>
		coupleMatcher.forEachMatch [
			val couple = createCouple()
			val p1 = personNameMatcher.getAllValuesOfp(p1name).head
			val p2 = personNameMatcher.getAllValuesOfp(p2name).head
			couple.setP1(p1)
			couple.setP2(p2)
			val commonMovies = commonMoviesMatcher.getAllValuesOfm(p1name, p2name)
			couple.commonMovies.addAll(commonMovies)
				
			newCouples += couple
		]
		
		println("# of couples = " + newCouples.size)
		engine.dispose
		addElementsToResource(newCouples);
	}

	// calculate the top group by rating
	def topGroupByRating(int size) { (*@\label{xform:topGroupByRating}@*)
		println("Top-15 by Average Rating")
		println("========================")
		val n = 15;
		
		val engine = IncQueryEngine.on(r)
		val coupleWithRatingMatcher = engine.groupSize
		val rankedCouples = coupleWithRatingMatcher.getAllValuesOfgroup(size).sort(
			new GroupAVGComparator)

		printCouples(n, rankedCouples)
	}

	// calculate the top group by common movies
	def topGroupByCommonMovies(int size) { (*@\label{xform:topGroupByCommonMovies}@*)
		println("Top-15 by Number of Common Movies")
		println("=================================")

		val n = 15;
		val engine = IncQueryEngine.on(r)
		val coupleWithRatingMatcher = engine.groupSize
		
		val rankedCouples = coupleWithRatingMatcher.getAllValuesOfgroup(size).sort(
			new GroupSizeComparator
		)
		printCouples(n, rankedCouples)
	}

	// pretty-print couples
	def printCouples(int n, List<Group> rankedCouples) {
		(0 .. n - 1).forEach [
			if(it < rankedCouples.size) {
				val c = rankedCouples.get(it);
				println(c.printGroup(it))
			}
		]
	}
	
	// pretty-print groups
	def printGroup(Group group, int lineNumber) {
		if(group instanceof Couple) {
			val couple = group as Couple
			return '''[guilleft]lineNumber[guilright]. Couple avgRating [guilleft]group.avgRating[guilright], [guilleft]group.commonMovies.size[guilright] movies ([guilleft]couple.p1.name[guilright]; [guilleft]couple.p2.name[guilright])'''
		}
		else {
			val clique = group as Clique
			return '''[guilleft]lineNumber[guilright]. [guilleft]clique.persons.size[guilright]-Clique avgRating [guilleft]group.avgRating[guilright], [guilleft]group.commonMovies.size[guilright] movies ([guilleft]
				FOR person : clique.persons SEPARATOR ", "[guilright][guilleft]person.name[guilright][guilleft]ENDFOR[guilright])'''
		}
	}

	// calculate average ratings	
	def calculateAvgRatings() { (*@\label{xform:calculateAvgRatings}@*)
		getElementsFromResource.filter(typeof(Group)).forEach[x|calculateAvgRating(x.commonMovies, x)]
	}

	// calculate average rating
	protected def calculateAvgRating(Collection<Movie> commonMovies, Group group) {
		var sumRating = 0.0

		for (m : commonMovies) {
			sumRating = sumRating + m.rating
		}
		val n = commonMovies.size
		group.avgRating = sumRating / n
	}

	// create cliques
	public def createCliques(int cliques) { (*@\label{xform:createCliques}@*)
		val engine = AdvancedIncQueryEngine.createUnmanagedEngine(r)
		val personMatcher = getPersonName(engine)
		var Collection<Clique> newCliques
		
		if(cliques == 3) {
			val clique3 = getPersonsTo3Clique(engine)
			
			newCliques = clique3.allMatches.map[x|generateClique(
				personMatcher.getOneArbitraryMatch(null,x.p1).p,
				personMatcher.getOneArbitraryMatch(null,x.p2).p,
				personMatcher.getOneArbitraryMatch(null,x.p3).p)].toList;
		}
		else if(cliques == 4) {
			val clique4 = getPersonsTo4Clique(engine)
			
			newCliques = clique4.allMatches.map[x|generateClique(
				personMatcher.getOneArbitraryMatch(null,x.p1).p,
				personMatcher.getOneArbitraryMatch(null,x.p2).p,
				personMatcher.getOneArbitraryMatch(null,x.p3).p,
				personMatcher.getOneArbitraryMatch(null,x.p4).p)].toList;
		}
		else if(cliques == 5) {
			val clique5 = getPersonsTo5Clique(engine)
			newCliques = clique5.allMatches.map[x|generateClique(
				personMatcher.getOneArbitraryMatch(null,x.p1).p,
				personMatcher.getOneArbitraryMatch(null,x.p2).p,
				personMatcher.getOneArbitraryMatch(null,x.p3).p,
				personMatcher.getOneArbitraryMatch(null,x.p4).p,
				personMatcher.getOneArbitraryMatch(null,x.p5).p)].toList;
		}
		
		println("# of "+cliques+"-cliques = " + newCliques.size)
		
		engine.dispose
		newCliques.forEach[x|x.commonMovies.addAll(x.collectCommonMovies)]
		addElementsToResource(newCliques);
	}
	
	// generate cliques
	protected def generateClique(Person... persons) {
		val c = createClique
		c.persons += persons
		return c
	}
	
	// collect common movies
	protected def collectCommonMovies(Clique clique) { (*@\label{xform:collectCommonMovies}@*)
		var Set<Movie> commonMovies = null;
		for(personMovies : clique.persons.map[movies]) {
			if(commonMovies == null) {
				commonMovies = personMovies.toSet;
			}
			else {
				commonMovies.retainAll(personMovies)
			}
		}
		return commonMovies
	}
}
