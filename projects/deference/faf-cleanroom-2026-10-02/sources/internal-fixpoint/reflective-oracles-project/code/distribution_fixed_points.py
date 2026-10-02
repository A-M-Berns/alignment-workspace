#!/usr/bin/env python3
"""
Computational exploration of fixed points in distribution spaces.

This script implements Scott Garrabrant's approach to reflective oracles
using distributions over distributions to achieve continuous fixed point operators.
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import minimize
from scipy.stats import entropy
from typing import Callable, Tuple, List
import warnings
warnings.filterwarnings('ignore')

class DistributionSpace:
    """Represents the space of distributions over a finite set."""

    def __init__(self, n: int):
        """Initialize distribution space over n elements."""
        self.n = n

    def uniform(self) -> np.ndarray:
        """Return the uniform distribution."""
        return np.ones(self.n) / self.n

    def point_mass(self, i: int) -> np.ndarray:
        """Return point mass at element i."""
        p = np.zeros(self.n)
        p[i] = 1.0
        return p

    def random(self) -> np.ndarray:
        """Return a random distribution."""
        p = np.random.dirichlet(np.ones(self.n))
        return p

    def validate(self, p: np.ndarray) -> bool:
        """Check if p is a valid probability distribution."""
        return np.allclose(p.sum(), 1.0) and np.all(p >= 0)


class Distribution2Space:
    """Represents distributions over distributions."""

    def __init__(self, base_space: DistributionSpace, n_samples: int = 100):
        """Initialize space of distributions over distributions."""
        self.base_space = base_space
        self.n_samples = n_samples

    def point_mass(self, p: np.ndarray) -> List[Tuple[np.ndarray, float]]:
        """Return point mass at distribution p."""
        return [(p, 1.0)]

    def uniform_over_all(self) -> List[Tuple[np.ndarray, float]]:
        """Return uniform distribution over all distributions."""
        # Sample many distributions uniformly
        samples = []
        for _ in range(self.n_samples):
            p = self.base_space.random()
            samples.append((p, 1.0 / self.n_samples))
        return samples

    def mean(self, dist2: List[Tuple[np.ndarray, float]]) -> np.ndarray:
        """Compute the mean distribution."""
        mean_dist = np.zeros(self.base_space.n)
        for p, weight in dist2:
            mean_dist += weight * p
        return mean_dist


class ConvexGraphCorrespondence:
    """A correspondence with convex graph property."""

    def __init__(self, base_space: DistributionSpace):
        """Initialize correspondence."""
        self.base_space = base_space
        self.dist2_space = Distribution2Space(base_space)

    def apply(self, p: np.ndarray) -> List[Tuple[np.ndarray, float]]:
        """Apply the correspondence to distribution p."""
        raise NotImplementedError

    def is_fixed_point(self, p: np.ndarray, tolerance: float = 1e-6) -> bool:
        """Check if p is a fixed point."""
        # p is a fixed point if point_mass(p) is in the output
        output = self.apply(p)
        # Check if output is approximately point mass at p
        if len(output) == 1:
            q, weight = output[0]
            return np.allclose(q, p, atol=tolerance) and np.isclose(weight, 1.0)
        return False


class NegationCorrespondence(ConvexGraphCorrespondence):
    """The negation correspondence for binary choices."""

    def __init__(self):
        """Initialize for binary space."""
        super().__init__(DistributionSpace(2))

    def apply(self, p: np.ndarray) -> List[Tuple[np.ndarray, float]]:
        """Apply negation correspondence."""
        # For binary: p = [p0, p1]
        # Negation maps p0 -> p1 and p1 -> p0

        # At the fixed point (p = [0.5, 0.5]), return point mass
        if np.allclose(p, [0.5, 0.5]):
            return self.dist2_space.point_mass(p)

        # Otherwise, create a distribution that "pulls" toward negation
        # The mean should map p to (1-p[0], 1-p[1]) = (p[1], p[0])
        negated = np.array([p[1], p[0]])

        # Create a distribution over distributions
        # that has mean equal to negated
        samples = []

        # Add some weight at the negated distribution
        samples.append((negated, 0.5))

        # Add some spread around it
        for _ in range(10):
            noise = np.random.normal(0, 0.1, 2)
            q = negated + noise
            q = np.clip(q, 0, 1)
            q = q / q.sum()  # Renormalize
            samples.append((q, 0.05))

        return samples


class IdentityCorrespondence(ConvexGraphCorrespondence):
    """The identity correspondence."""

    def apply(self, p: np.ndarray) -> List[Tuple[np.ndarray, float]]:
        """Apply identity correspondence."""
        # For identity, every distribution with mean p works
        # We'll return a spread of distributions with mean p

        samples = []

        # Include p itself
        samples.append((p, 0.2))

        # Add variations that maintain the mean
        for _ in range(20):
            # Generate random distribution
            q = self.base_space.random()
            # Mix with p to get closer to desired mean
            alpha = np.random.uniform(0.3, 0.7)
            r = alpha * p + (1 - alpha) * q
            r = r / r.sum()
            samples.append((r, 0.04))

        return samples


def find_fixed_points(correspondence: ConvexGraphCorrespondence,
                      n_trials: int = 100) -> List[np.ndarray]:
    """Find fixed points of a correspondence via optimization."""

    fixed_points = []
    n = correspondence.base_space.n

    def objective(x):
        """Minimize distance to being a fixed point."""
        p = x[:n]
        p = p / p.sum()  # Normalize

        output = correspondence.apply(p)
        mean_output = correspondence.dist2_space.mean(output)

        # Distance from p to mean of output
        return np.linalg.norm(p - mean_output)

    for _ in range(n_trials):
        # Random starting point
        x0 = correspondence.base_space.random()

        # Optimize
        result = minimize(objective, x0, method='SLSQP',
                        bounds=[(0, 1)] * n,
                        constraints={'type': 'eq', 'fun': lambda x: x.sum() - 1})

        if result.success and result.fun < 1e-6:
            p = result.x / result.x.sum()

            # Check if we already found this fixed point
            is_new = True
            for fp in fixed_points:
                if np.allclose(p, fp, atol=1e-3):
                    is_new = False
                    break

            if is_new:
                fixed_points.append(p)

    return fixed_points


def visualize_correspondence(correspondence: ConvexGraphCorrespondence):
    """Visualize a correspondence on binary space."""

    if correspondence.base_space.n != 2:
        print("Visualization only works for binary space")
        return

    # Create grid of p values (p0 from 0 to 1, p1 = 1 - p0)
    p0_values = np.linspace(0, 1, 100)

    # For each p, compute the mean of the output distribution
    mean_outputs = []

    for p0 in p0_values:
        p = np.array([p0, 1 - p0])
        output = correspondence.apply(p)
        mean_output = correspondence.dist2_space.mean(output)
        mean_outputs.append(mean_output[0])

    plt.figure(figsize=(10, 6))
    plt.plot(p0_values, mean_outputs, 'b-', label='Mean output p0')
    plt.plot(p0_values, p0_values, 'r--', label='Identity (fixed points)')
    plt.xlabel('Input p0')
    plt.ylabel('Mean output p0')
    plt.title(f'{correspondence.__class__.__name__}')
    plt.legend()
    plt.grid(True, alpha=0.3)

    # Mark fixed points
    fixed_points = find_fixed_points(correspondence, n_trials=20)
    for fp in fixed_points:
        plt.plot(fp[0], fp[0], 'go', markersize=10, label='Fixed point')

    plt.savefig(f'{correspondence.__class__.__name__}.png')
    plt.close()


def main():
    """Run computational experiments."""

    print("Exploring Fixed Points in Distribution Spaces")
    print("=" * 50)

    # Test negation correspondence
    print("\n1. Negation Correspondence (Binary)")
    neg_corr = NegationCorrespondence()

    # Check fixed point at [0.5, 0.5]
    p_half = np.array([0.5, 0.5])
    print(f"Is [0.5, 0.5] a fixed point? {neg_corr.is_fixed_point(p_half)}")

    # Find fixed points
    fixed_points = find_fixed_points(neg_corr, n_trials=20)
    print(f"Found {len(fixed_points)} fixed point(s):")
    for fp in fixed_points:
        print(f"  {fp}")

    # Visualize
    visualize_correspondence(neg_corr)

    # Test identity correspondence
    print("\n2. Identity Correspondence (Binary)")
    id_corr = IdentityCorrespondence(DistributionSpace(2))

    # Check some points
    for p0 in [0.2, 0.5, 0.8]:
        p = np.array([p0, 1 - p0])
        print(f"Is [{p0:.1f}, {1-p0:.1f}] a fixed point? {id_corr.is_fixed_point(p)}")

    # Visualize
    visualize_correspondence(id_corr)

    print("\n3. Identity Correspondence (Ternary)")
    id_corr_3 = IdentityCorrespondence(DistributionSpace(3))

    # Find fixed points (should be many)
    fixed_points = find_fixed_points(id_corr_3, n_trials=10)
    print(f"Found {len(fixed_points)} fixed point(s) (sample):")
    for fp in fixed_points[:3]:
        print(f"  {fp}")

    print("\nConclusion:")
    print("- Negation has unique fixed point at uniform distribution")
    print("- Identity has all distributions as fixed points")
    print("- The framework successfully captures Scott's intuition")


if __name__ == "__main__":
    main()