import unittest

from compare_scores import (
    EXAMPLES, Example, dominates, ideal_span_envelope, weighted_round_preference,
    minimum_unit_schedule, unit_dag_metrics,
)


class ScoringTradeoffs(unittest.TestCase):
    def test_round_and_span_frontiers_can_disagree(self):
        parallel, serial, _ = EXAMPLES
        self.assertFalse(dominates(parallel.point("oracle_rounds"), serial.point("oracle_rounds")))
        self.assertFalse(dominates(serial.point("oracle_rounds"), parallel.point("oracle_rounds")))
        self.assertTrue(dominates(parallel.point("span"), serial.point("span")))

    def test_weight_changes_ranking_and_is_a_policy_choice(self):
        parallel, serial, _ = EXAMPLES
        self.assertLess(weighted_round_preference(parallel, 0), weighted_round_preference(serial, 0))
        self.assertGreater(weighted_round_preference(parallel, 10_000), weighted_round_preference(serial, 10_000))

    def test_rounds_times_bytes_can_hide_enormous_work(self):
        parallel, _, expensive = EXAMPLES
        self.assertLess(expensive.oracle_rounds * expensive.proof_bytes,
                        parallel.oracle_rounds * parallel.proof_bytes)
        self.assertGreater(expensive.work, 90 * parallel.work)
        self.assertFalse(dominates(expensive.point("oracle_rounds"), parallel.point("oracle_rounds")))

    def test_lower_bound_is_not_the_scheduling_upper_envelope(self):
        for e in EXAMPLES:
            lower, upper = ideal_span_envelope(e, 64)
            self.assertLess(lower, upper)

    def test_equal_work_span_can_have_different_finite_worker_time(self):
        barrier = (frozenset(), frozenset(), frozenset(),
                   frozenset({0, 1, 2}), frozenset({0, 1, 2}), frozenset({0, 1, 2}))
        chains = (frozenset(), frozenset({0}), frozenset(),
                  frozenset({2}), frozenset(), frozenset({4}))
        self.assertEqual(unit_dag_metrics(barrier), (6, 2))
        self.assertEqual(unit_dag_metrics(chains), (6, 2))
        self.assertEqual(minimum_unit_schedule(barrier, 2), 4)
        self.assertEqual(minimum_unit_schedule(chains, 2), 3)
        self.assertLess(max(6 // 2, 2), minimum_unit_schedule(barrier, 2))

    def test_inflated_work_upper_bound_cannot_improve_pareto_point(self):
        honest = (100, 1000, 100)
        inflated = (10**12, 1000, 100)
        self.assertGreater(inflated[0] / inflated[2], honest[0] / honest[2])
        self.assertTrue(dominates(honest, inflated))

    def test_invalid_models_and_worker_counts_are_rejected(self):
        for workers in (0, -1, True):
            with self.assertRaises(ValueError):
                ideal_span_envelope(EXAMPLES[0], workers)
        with self.assertRaises(ValueError):
            Example("impossible", 1, 1, 1, 2)
        with self.assertRaises(ValueError):
            EXAMPLES[0].point("tree-height")
        with self.assertRaises(ValueError):
            dominates((1, 2), (1, 2, 3))


if __name__ == "__main__":
    unittest.main()
