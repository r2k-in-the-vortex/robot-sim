//! Every theorem of `lean/TorqueWrench.lean` and `lean/Dynamics.lean` that states a law of the
//! algebra, restated as an executable property and named after its theorem.
//!
//! The Lean proofs are the specification; these tests are the Rust read of them. Each one is
//! `==` over the exact rationals — no tolerance, no epsilon — because both files are stated over
//! an arbitrary `CommRing`, so every law in them is a polynomial identity, and a polynomial
//! identity that holds over `ℚ` holds in the field the app will actually use.
//!
//! The rotations are generated from Pythagorean pairs, so `cos² + sin² = 1` and `det = 1` hold
//! exactly and stay inside the rationals; nothing anywhere in this file needs a transcendental.
//! The properties the theorems *hypothesize* — orthogonality, determinant one, inertia symmetry —
//! are carried by [`Rotation`] and [`MassProperties`], which is why no test states them again:
//! the type is the hypothesis.

use robot_dynamics::{
    Accel, MassProperties, Rotation, Twist, Wrench, com_accel, first_moment, gravity_wrench,
    inertial_wrench, measured_wrench, origin_inertia, parallel_axis_inertia,
    recovered_contact_wrench, sensor_accel_to_tip, sensor_mass_to_tip, sensor_to_tip,
    sensor_twist_to_tip, spatial_gravity_wrench, spatial_inertial_wrench, tip_accel_to_sensor,
    tip_mass_to_sensor, tip_to_sensor, tip_twist_to_sensor, virtual_work,
};
use robot_golden::Ratio as R;
use robot_kinematics::{Field, Mat3, Vec3};

// ---- data ------------------------------------------------------------------

fn q(numerator: i128, denominator: i128) -> R {
    R::new(numerator, denominator)
}

/// A small integer as a field element: `Vec3` and `Mat3` take `S`, and an `i128` literal does
/// not become a `Ratio` on its own.
fn ri(value: i128) -> R {
    R::integer(value)
}

/// A 3x3 block of integer entries.
fn mat(rows: [[i128; 3]; 3]) -> Mat3<R> {
    let mut out = Mat3::from_rows([[R::zero(); 3]; 3]);
    for (i, row) in rows.iter().enumerate() {
        for (j, &entry) in row.iter().enumerate() {
            out.set(i, j, ri(entry));
        }
    }
    out
}

/// Three vectors as a 3x3 block in the order given — `from_rows` and `from_cols` take the bare
/// arrays, and a `Vec3` is not one.
fn block(a: Vec3<R>, b: Vec3<R>, c: Vec3<R>) -> [[R; 3]; 3] {
    [*a.as_array(), *b.as_array(), *c.as_array()]
}

fn v(x: i128, y: i128, z: i128) -> Vec3<R> {
    Vec3::from([R::integer(x), R::integer(y), R::integer(z)])
}

/// A rotation from an explicit exact cosine/sine pair; `None` would mean `cos² + sin² ≠ 1`, so
/// the `expect` is the unit-circle assertion.
fn rot_x(cos: (i128, i128), sin: (i128, i128)) -> Rotation<R> {
    Rotation::rot_x_cs(R::pair(cos, sin)).expect("cos^2 + sin^2 = 1")
}

fn rot_y(cos: (i128, i128), sin: (i128, i128)) -> Rotation<R> {
    Rotation::rot_y_cs(R::pair(cos, sin)).expect("cos^2 + sin^2 = 1")
}

fn rot_z(cos: (i128, i128), sin: (i128, i128)) -> Rotation<R> {
    Rotation::rot_z_cs(R::pair(cos, sin)).expect("cos^2 + sin^2 = 1")
}

/// Rotations, all from exact Pythagorean pairs: identity, one of each axis, a quarter turn, the
/// two *other* square roots of the identity, and compositions of them — including one about two
/// different axes, which is where a shared-axis mistake would hide.
fn rotations() -> Vec<Rotation<R>> {
    vec![
        Rotation::identity(),
        rot_x((3, 5), (4, 5)),
        rot_y((5, 13), (12, 13)),
        rot_z((8, 17), (15, 17)),
        rot_z((0, 1), (1, 1)),   // a quarter turn about z
        rot_x((-1, 1), (0, 1)),  // a half turn about x: the first square root of the identity
        rot_y((0, 1), (-1, 1)),  // a quarter turn the other way about y
        rot_x((3, 5), (4, 5)) * rot_z((8, 17), (15, 17)),
        rot_z((0, 1), (1, 1)) * rot_x((0, 1), (1, 1)),
    ]
}

/// Lever arms into `tipToSensor` and friends: the origin, the three axes, a negative component,
/// and one that is not integral — a lever arm scales every `p × F` term, so a non-integral one
/// is what catches a dropped factor.
fn offsets() -> Vec<Vec3<R>> {
    vec![
        v(0, 0, 0),
        v(1, 0, 0),
        v(0, -2, 0),
        v(0, 0, 3),
        v(2, -5, 1),
        Vec3::from([q(1, 2), q(-3, 4), q(2, 3)]),
    ]
}

fn vectors() -> Vec<Vec3<R>> {
    vec![
        v(0, 0, 0),
        v(1, 0, 0),
        v(0, 1, 0),
        v(0, 0, 1),
        v(1, 2, -3),
        v(-4, 5, 6),
        Vec3::from([q(2, 3), q(-1, 5), q(7, 2)]),
    ]
}

fn twists() -> Vec<Twist<R>> {
    vec![
        Twist::zero(),
        Twist::new(v(1, 0, 0), v(0, 0, 0)),
        Twist::new(v(2, -1, 3), v(0, 4, -2)),
        Twist::new(v(0, 0, 0), v(1, 1, 0)),
        Twist::new(v(-1, 0, 2), v(3, 0, -5)),
    ]
}

/// Acceleration is the part of the data that is *not* frame-independent, so the list leans on
/// the cases where the centripetal term is the thing under test: `ω ≠ 0` with `c ≠ 0` and
/// `α` non-zero on all three axes.
fn accels() -> Vec<Accel<R>> {
    vec![
        Accel::zero(),
        Accel::new(v(1, 0, 0), v(0, 0, 0)),
        Accel::new(v(-2, 3, -4), v(5, -6, 7)),
        Accel::new(v(0, 0, 9), v(0, -1, 0)),
        Accel::new(Vec3::from([q(1, 2), ri(0), q(-5, 3)]), v(1, 1, 1)),
    ]
}

/// Bodies: symmetric inertias, one diagonal and one fully dense, centres of mass on and off the
/// origin, and one with a fractional mass. `MassProperties::new` screens the symmetry, so an
/// asymmetric entry cannot enter the tests at all.
fn bodies() -> Vec<MassProperties<R>> {
    vec![
        MassProperties::new(
            R::integer(1),
            v(0, 0, 0),
            mat([[1, 0, 0], [0, 1, 0], [0, 0, 1]]),
        )
        .expect("diagonal"),
        MassProperties::new(
            R::integer(2),
            v(1, 0, 0),
            mat([[2, 0, 0], [0, 3, 0], [0, 0, 4]]),
        )
        .expect("diagonal with an offset centre of mass"),
        MassProperties::new(
            R::integer(3),
            v(-1, 2, 1),
            mat([[4, 1, -2], [1, 5, 3], [-2, 3, 6]]),
        )
        .expect("symmetric, fully dense"),
        MassProperties::new(
            q(1, 2),
            Vec3::from([q(1, 3), q(-2, 5), ri(0)]),
            mat([[1, 0, 1], [0, 2, 0], [1, 0, 3]]),
        )
        .expect("symmetric, fractional mass"),
    ]
}

fn gravities() -> Vec<Vec3<R>> {
    vec![
        v(0, 0, 0),
        v(0, 0, -9),
        v(0, 0, -1),
        v(1, -2, -3),
        Vec3::from([q(1, 7), ri(0), q(-9, 2)]),
    ]
}

fn wrenches() -> Vec<Wrench<R>> {
    vec![
        Wrench::zero(),
        Wrench::new(v(1, 0, 0), v(0, 0, 0)),
        Wrench::new(v(0, 0, 5), v(0, -3, 0)),
        Wrench::new(v(-2, 4, 1), v(3, -1, 7)),
        Wrench::new(
            Vec3::from([q(1, 2), q(-3, 2), ri(0)]),
            Vec3::from([ri(0), q(5, 4), q(-1, 8)]),
        ),
    ]
}

/// `a + b` for the 3x3 inertia blocks; the kinematics `Mat3` deliberately carries only the
/// product, and widening it would touch a frozen API for one test.
fn mat_add(left: Mat3<R>, right: Mat3<R>) -> Mat3<R> {
    let mut sum = left;
    for i in 0..3 {
        for j in 0..3 {
            sum.set(i, j, left.at(i, j) + right.at(i, j));
        }
    }
    sum
}

fn mat_sub(left: Mat3<R>, right: Mat3<R>) -> Mat3<R> {
    let mut difference = left;
    for i in 0..3 {
        for j in 0..3 {
            difference.set(i, j, left.at(i, j) - right.at(i, j));
        }
    }
    difference
}

/// The composite of two rigidly attached bodies, built from the three quantities the Lean
/// composition theorems say add: mass, first moment, and inertia about the common origin.
///
/// The centre of mass is the one quantity that does **not** add — it is `h / m`, the only
/// division in the whole model — which is exactly why Lean states `inertialWrench_add` on
/// `(mass, firstMoment, originInertia)` and never forms `c` at all: that form holds over any
/// commutative ring, this one needs a field.
fn composite(one: MassProperties<R>, two: MassProperties<R>) -> MassProperties<R> {
    let mass = one.mass() + two.mass();
    let first = first_moment(one) + first_moment(two);
    let origin = mat_add(origin_inertia(one), origin_inertia(two));
    let com = first.scale(R::one() / mass);
    let inertia = mat_sub(origin, parallel_axis_inertia(mass, com));
    MassProperties::new(mass, com, inertia).expect("the summed inertia is symmetric")
}

/// The composite of two of the listed bodies, paired so the parts differ from each other.
fn composites() -> Vec<(MassProperties<R>, MassProperties<R>, MassProperties<R>)> {
    let bodies = bodies();
    let mut out = Vec::new();
    for i in 0..bodies.len() {
        for j in (i + 1)..bodies.len() {
            out.push((bodies[i], bodies[j], composite(bodies[i], bodies[j])));
        }
    }
    out
}

// ---- the frame algebra: TorqueWrench.lean ----------------------------------

/// `virtualWork_invariant`: work is the same number in either frame.
///
/// This is the coherence condition on the pair of transforms — the wrench is a covector and the
/// twist a vector, and the two move dually, so the pairing is invariant. Both sides here use the
/// *one* twist stated in the case, resolved in the two frames, which is the shape Lean states
/// (`virtualWork_invariant`, the rational instance of `virtualWork_invariant_real`).
#[test]
fn virtual_work_invariant() {
    for (i, p) in offsets().into_iter().enumerate() {
        for (j, r) in rotations().into_iter().enumerate() {
            for (k, w) in wrenches().into_iter().enumerate() {
                for (m, t) in twists().into_iter().enumerate() {
                    let sensor_work = virtual_work(tip_to_sensor(p, r, w), t);
                    let tip_work = virtual_work(w, sensor_twist_to_tip(p, r, t));
                    assert_eq!(
                        sensor_work, tip_work,
                        "p[{i}] R[{j}] w[{k}] t[{m}]"
                    );
                }
            }
        }
    }
}

/// `sensorToTip_tipToSensor`: converting a tip wrench up to the sensor frame and back is
/// lossless. Stated for every wrench, the two directions being different theorems in Lean
/// because each consumes a different one of the two orthogonality readings.
#[test]
fn sensor_to_tip_tip_to_sensor() {
    for p in offsets() {
        for r in rotations() {
            for w in wrenches() {
                assert_eq!(sensor_to_tip(p, r, tip_to_sensor(p, r, w)), w);
            }
        }
    }
}

/// `tipToSensor_sensorToTip`: the same round trip starting from a sensor-frame wrench.
#[test]
fn tip_to_sensor_sensor_to_tip() {
    for p in offsets() {
        for r in rotations() {
            for w in wrenches() {
                assert_eq!(tip_to_sensor(p, r, sensor_to_tip(p, r, w)), w);
            }
        }
    }
}

/// `sensorTwistToTip_tipTwistToSensor`: the twist round trip in the direction that loses the
/// lever arm first.
#[test]
fn sensor_twist_to_tip_tip_twist_to_sensor() {
    for p in offsets() {
        for r in rotations() {
            for t in twists() {
                assert_eq!(sensor_twist_to_tip(p, r, tip_twist_to_sensor(p, r, t)), t);
            }
        }
    }
}

/// `tipTwistToSensor_sensorTwistToTip`: the other direction. Together with the previous test
/// this says the two twist transforms are mutual inverses, so a motion can be moved between the
/// frames in either order without loss.
#[test]
fn tip_twist_to_sensor_sensor_twist_to_tip() {
    for p in offsets() {
        for r in rotations() {
            for t in twists() {
                assert_eq!(tip_twist_to_sensor(p, r, sensor_twist_to_tip(p, r, t)), t);
            }
        }
    }
}

/// `mulVec_cross`: a rotation commutes with the cross product.
///
/// This is where `det = 1` earns its place. Orthogonality alone admits reflections, and a
/// reflection *anti*-commutes with the cross product, so a `Rotation` built only from `Rᵀ R = 1`
/// would pass every round trip above and still get the torque of a transported wrench wrong.
#[test]
fn mul_vec_cross() {
    for r in rotations() {
        for u in vectors() {
            for q in vectors() {
                assert_eq!(
                    r.mul_vec(u.cross(q)),
                    r.mul_vec(u).cross(r.mul_vec(q))
                );
            }
        }
    }
}

/// `Rotation.transpose_mulVec_cross`: read the same law backwards through the inverse rotation,
/// which moves the *other* factor across. `sensorTwistToTip_comp` below is where this is used.
#[test]
fn transpose_mul_vec_cross() {
    for r in rotations() {
        for u in vectors() {
            for q in vectors() {
                assert_eq!(
                    r.transpose_mul_vec(u).cross(q),
                    r.transpose_mul_vec(u.cross(r.mul_vec(q)))
                );
            }
        }
    }
}

/// `Rotation.cross_transpose`: with both factors transposed, a cross product transports as a
/// whole — the form `sensorAccelToTip_comp` pushes each `σᵀ` inside with.
#[test]
fn rotation_cross_transpose() {
    for r in rotations() {
        for u in vectors() {
            for q in vectors() {
                assert_eq!(
                    r.transpose_mul_vec(u).cross(r.transpose_mul_vec(q)),
                    r.transpose_mul_vec(u.cross(q))
                );
            }
        }
    }
}

/// `mulVec_dotProduct`: the transpose moves across a dot product. The consequence tested
/// alongside it is the one orthogonality is *for*: a rotation preserves the inner product, so
/// norms, distances and angles are frame-independent.
#[test]
fn mul_vec_dot_product() {
    for r in rotations() {
        for u in vectors() {
            for q in vectors() {
                assert_eq!(
                    r.mul_vec(u).dot(q),
                    u.dot(r.transpose_mul_vec(q))
                );
                assert_eq!(r.mul_vec(u).dot(r.mul_vec(q)), u.dot(q));
            }
        }
    }
}

/// `cross_dotProduct_eq_det`: the triple product of `u`, `q`, `w` is the determinant of the
/// block they form. The block is built by columns here, which is Lean's `![u, v, w]` block
/// transposed — the determinant cannot tell the difference, and that is the only reason the two
/// statements are the same one. `Mat3::det` is also the determinant `Rotation::new` tests
/// against one, so this pins the dot/cross/determinant conventions of the frozen kinematics API
/// to the ones the Lean algebra assumes.
#[test]
fn cross_dot_product_eq_det() {
    for u in vectors() {
        for q in vectors() {
            for w in vectors() {
                assert_eq!(
                    u.cross(q).dot(w),
                    Mat3::from_cols(block(u, q, w)).det()
                );
            }
        }
    }
}

/// `det_rotate`: rotating the three rows of a block leaves its determinant alone, because the
/// block is multiplied by `Rᵀ` and `det R = 1`. This is the step that turns `R` into a change of
/// basis inside `mulVec_cross`.
#[test]
fn det_rotate() {
    for r in rotations() {
        for u in vectors() {
            for q in vectors() {
                for w in vectors() {
                    let rotated =
                        Mat3::from_rows(block(r.mul_vec(u), r.mul_vec(q), r.mul_vec(w))).det();
                    let original = Mat3::from_rows(block(u, q, w)).det();
                    assert_eq!(rotated, original);
                }
            }
        }
    }
}

/// `Rotation.mul_mat`: composition of rotations is composition of their matrices, and the
/// composed rotation's own matrix really is orthogonal with determinant one.
///
/// The two orthogonality readings are both asserted because `mul_transpose_eq_one` is a theorem
/// and not a definition: Lean derives `R * Rᵀ = 1` from `Rᵀ * R = 1` *plus* `det R = 1`, and the
/// twist round trip that consumes the second reading is where that derivation is spent.
#[test]
fn rotation_mul_mat() {
    for r in rotations() {
        for s in rotations() {
            assert_eq!((r * s).mat(), r.mat() * s.mat());
            assert_eq!((r * s).mat().det(), R::one());
            assert_eq!((r * s).mat().transpose() * (r * s).mat(), Mat3::identity());
            assert_eq!((r * s).mat() * (r * s).mat().transpose(), Mat3::identity());
            // `Rotation.inv`, the `ρ⁻¹` that `cross_transpose` is proved through
            assert!((r * r.inverse()).is_identity());
            assert!((r.inverse() * r).is_identity());
        }
    }
}

/// `tipToSensor_comp`: routing a wrench through a middle frame is the same as converting it once
/// through the composed pose. The lever arms merge because a rotation commutes with `cross` —
/// this theorem is why `mulVec_cross` had to be proved over a genuine rotation.
#[test]
fn tip_to_sensor_comp() {
    for p in offsets() {
        for q in offsets() {
            for r in rotations() {
                for s in rotations() {
                    for w in wrenches() {
                        assert_eq!(
                            tip_to_sensor(p, r, tip_to_sensor(q, s, w)),
                            tip_to_sensor(p + r.mul_vec(q), r * s, w)
                        );
                    }
                }
            }
        }
    }
}

/// `sensorTwistToTip_comp`: twists fold through a chain exactly like wrenches, with the same
/// composed pose.
#[test]
fn sensor_twist_to_tip_comp() {
    for p in offsets() {
        for q in offsets() {
            for r in rotations() {
                for s in rotations() {
                    for t in twists() {
                        assert_eq!(
                            sensor_twist_to_tip(q, s, sensor_twist_to_tip(p, r, t)),
                            sensor_twist_to_tip(p + r.mul_vec(q), r * s, t)
                        );
                    }
                }
            }
        }
    }
}

// ---- the sensor dynamics: Dynamics.lean ------------------------------------

/// `tipAccelToSensor_sensorAccelToTip`: the acceleration round trip, tip-bound-first direction.
/// Note that it needs the twist as well as the acceleration: unlike a velocity, an acceleration
/// is frame-dependent through the frame's own rotation, so it has to be told how the sensor is
/// turning.
#[test]
fn tip_accel_to_sensor_sensor_accel_to_tip() {
    for p in offsets() {
        for r in rotations() {
            for t in twists() {
                for acc in accels() {
                    assert_eq!(
                        tip_accel_to_sensor(
                            p,
                            r,
                            sensor_twist_to_tip(p, r, t),
                            sensor_accel_to_tip(p, r, t, acc)
                        ),
                        acc
                    );
                }
            }
        }
    }
}

/// `sensorAccelToTip_tipAccelToSensor`: the same round trip the other way round, told the twist
/// in the frame the acceleration starts in. This is the direction the measurement model uses.
#[test]
fn sensor_accel_to_tip_tip_accel_to_sensor() {
    for p in offsets() {
        for r in rotations() {
            for t in twists() {
                for acc in accels() {
                    assert_eq!(
                        sensor_accel_to_tip(
                            p,
                            r,
                            tip_twist_to_sensor(p, r, t),
                            tip_accel_to_sensor(p, r, t, acc)
                        ),
                        acc
                    );
                }
            }
        }
    }
}

/// `sensorMassToTip_tipMassToSensor`: a body's description can be moved up to the sensor frame
/// and back without loss — the centre of mass and the inertia tensor both come home.
#[test]
fn sensor_mass_to_tip_tip_mass_to_sensor() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                assert_eq!(sensor_mass_to_tip(p, r, tip_mass_to_sensor(p, r, mp)), mp);
            }
        }
    }
}

/// `tipMassToSensor_sensorMassToTip`: and the same starting from the sensor-frame description.
/// The pair is what lets mass properties identified in either frame be used in the other.
#[test]
fn tip_mass_to_sensor_sensor_mass_to_tip() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                assert_eq!(tip_mass_to_sensor(p, r, sensor_mass_to_tip(p, r, mp)), mp);
            }
        }
    }
}

/// `comAccel_transport`: the material-point acceleration of the centre of mass is
/// frame-independent — computed from the sensor-frame description of the body and the motion,
/// it is the rotation of the tip-frame one.
///
/// This is the isolated non-linear step under the two covariance theorems below. It needs
/// `det = 1` as well as orthogonality, through `mulVec_cross`; and it needs the *twist* as well
/// as the acceleration, because the centripetal term `ω × (ω × p)` is quadratic in the motion.
#[test]
fn com_accel_transport() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                for t in twists() {
                    for acc in accels() {
                        let sensor_side = com_accel(
                            tip_mass_to_sensor(p, r, mp),
                            tip_twist_to_sensor(p, r, t),
                            tip_accel_to_sensor(p, r, t, acc),
                        );
                        assert_eq!(sensor_side, r.mul_vec(com_accel(mp, t, acc)));
                    }
                }
            }
        }
    }
}

/// `inertialWrench_transport`: **covariance of the inertial wrench.** The wrench computed in the
/// sensor frame from the sensor-frame body and motion equals the tip-frame wrench transported
/// up. So identified mass properties may be used in either frame, and the model is a description
/// of the body rather than of the frame it happens to be written in.
#[test]
fn inertial_wrench_transport() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                for t in twists() {
                    for acc in accels() {
                        let sensor_side = inertial_wrench(
                            tip_mass_to_sensor(p, r, mp),
                            tip_twist_to_sensor(p, r, t),
                            tip_accel_to_sensor(p, r, t, acc),
                        );
                        assert_eq!(
                            tip_to_sensor(p, r, inertial_wrench(mp, t, acc)),
                            sensor_side
                        );
                    }
                }
            }
        }
    }
}

/// `gravityWrench_transport`: with the gravity vector rotated into the sensor frame, the
/// gravitational wrench transports like any other wrench applied at the centre of mass. This is
/// the theorem an implementation uses to get a world-frame `g` into a sensor frame.
#[test]
fn gravity_wrench_transport() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                for g in gravities() {
                    assert_eq!(
                        tip_to_sensor(p, r, gravity_wrench(mp, g)),
                        gravity_wrench(tip_mass_to_sensor(p, r, mp), r.mul_vec(g))
                    );
                }
            }
        }
    }
}

/// `dot_mulVec_self`: the inertia tensor is symmetric, so it may be paired with either factor.
/// This is what makes the angular power `α ⋅ (I ω)` legitimate rather than `(I α) ⋅ ω`, and it
/// is the only place the symmetry bundled in `MassProperties` is used.
#[test]
fn dot_mul_vec_self() {
    for mp in bodies() {
        for u in vectors() {
            for w in vectors() {
                assert_eq!(
                    mp.inertia().mul_vec(u).dot(w),
                    u.dot(mp.inertia().mul_vec(w))
                );
            }
        }
    }
}

/// `virtualWork_inertialWrench_mul_vec`: the power the inertial wrench delivers, read straight
/// off the definition — mass times the centred acceleration against the centred velocity, plus
/// `(I α) ⋅ ω`.
///
/// Neither the gyroscopic torque `ω × (I ω)` nor the lever-arm torque `c × F` appears: they
/// cancel out of the power. That cancellation is what makes this identity the algebraic stand-in
/// for `d/dt (kinetic energy) = power` with no derivative anywhere.
#[test]
fn virtual_work_inertial_wrench_mul_vec() {
    for mp in bodies() {
        for t in twists() {
            for acc in accels() {
                let centred_velocity = t.v + t.omega.cross(mp.com());
                assert_eq!(
                    virtual_work(inertial_wrench(mp, t, acc), t),
                    mp.mass() * com_accel(mp, t, acc).dot(centred_velocity)
                        + mp.inertia().mul_vec(acc.alpha).dot(t.omega)
                );
            }
        }
    }
}

/// `virtualWork_inertialWrench`: the same power in its classical form, the angular acceleration
/// against the angular momentum `I ω`. The two forms agree exactly because the inertia is
/// symmetric (`dot_mulVec_self`), which is the point of that theorem.
#[test]
fn virtual_work_inertial_wrench() {
    for mp in bodies() {
        for t in twists() {
            for acc in accels() {
                let centred_velocity = t.v + t.omega.cross(mp.com());
                assert_eq!(
                    virtual_work(inertial_wrench(mp, t, acc), t),
                    mp.mass() * com_accel(mp, t, acc).dot(centred_velocity)
                        + acc.alpha.dot(mp.inertia().mul_vec(t.omega))
                );
            }
        }
    }
}

/// `virtualWork_gravityWrench`: `m g` acting at the centre of mass, which is `m` times `g`
/// against the **centred** velocity — the rate at which gravitational potential energy is lost.
///
/// This is also the sign check for the whole gravity convention: a tool held still against
/// gravity has the sensor delivering the negative of it.
#[test]
fn virtual_work_gravity_wrench() {
    for mp in bodies() {
        for g in gravities() {
            for t in twists() {
                assert_eq!(
                    virtual_work(gravity_wrench(mp, g), t),
                    mp.mass() * g.dot(t.v + t.omega.cross(mp.com()))
                );
            }
        }
    }
}

/// `inertialWrench_origin_form`: the inertial wrench written in terms of the additive triple
/// — mass, first moment, and inertia *about the frame origin*. The origin form is the one that
/// exposes what a body contributes and what adds when bodies are joined.
#[test]
fn inertial_wrench_origin_form() {
    for mp in bodies() {
        for t in twists() {
            for acc in accels() {
                assert_eq!(
                    inertial_wrench(mp, t, acc),
                    spatial_inertial_wrench(
                        mp.mass(),
                        first_moment(mp),
                        origin_inertia(mp),
                        t,
                        acc
                    )
                );
            }
        }
    }
}

/// `gravityWrench_firstMoment`: gravity sees the body only through its mass and first moment.
#[test]
fn gravity_wrench_first_moment() {
    for mp in bodies() {
        for g in gravities() {
            assert_eq!(
                gravity_wrench(mp, g),
                spatial_gravity_wrench(mp.mass(), first_moment(mp), g)
            );
        }
    }
}

/// `spatialInertialWrench_add`: the spatial inertial wrench is additive in its triple — masses,
/// first moments and inertias about a common origin all add. This is the composition law for
/// rigidly attached bodies, and it holds over *any* commutative ring because the triple never
/// has to be recombined into a centre of mass.
#[test]
fn spatial_inertial_wrench_add() {
    for one in bodies() {
        for two in bodies() {
            for t in twists() {
                for acc in accels() {
                    let (m1, h1, i1) = (one.mass(), first_moment(one), origin_inertia(one));
                    let (m2, h2, i2) = (two.mass(), first_moment(two), origin_inertia(two));
                    assert_eq!(
                        spatial_inertial_wrench(
                            m1 + m2,
                            h1 + h2,
                            mat_add(i1, i2),
                            t,
                            acc
                        ),
                        spatial_inertial_wrench(m1, h1, i1, t, acc)
                            + spatial_inertial_wrench(m2, h2, i2, t, acc)
                    );
                }
            }
        }
    }
}

/// `spatialGravityWrench_add`: the same law for gravity, which needs only the mass and the
/// first moment.
#[test]
fn spatial_gravity_wrench_add() {
    for one in bodies() {
        for two in bodies() {
            for g in gravities() {
                let (m1, h1) = (one.mass(), first_moment(one));
                let (m2, h2) = (two.mass(), first_moment(two));
                assert_eq!(
                    spatial_gravity_wrench(m1 + m2, h1 + h2, g),
                    spatial_gravity_wrench(m1, h1, g)
                        + spatial_gravity_wrench(m2, h2, g)
                );
            }
        }
    }
}

/// `inertialWrench_add`: a body whose mass, first moment and origin inertia are the sums of two
/// parts' has, at the same motion, the inertial wrench that is the sum of the parts' wrenches —
/// tool plus payload folds into one body, which is the composition an app with a tool changer
/// depends on.
#[test]
fn inertial_wrench_add() {
    for (one, two, whole) in composites() {
        for t in twists() {
            for acc in accels() {
                assert_eq!(
                    inertial_wrench(whole, t, acc),
                    inertial_wrench(one, t, acc) + inertial_wrench(two, t, acc)
                );
            }
        }
    }
}

/// `gravityWrench_add`: the same composition law for gravity, needing only mass and first
/// moment — so a payload's gravity wrench is independent of how its inertia is distributed.
#[test]
fn gravity_wrench_add() {
    for (one, two, whole) in composites() {
        for g in gravities() {
            assert_eq!(
                gravity_wrench(whole, g),
                gravity_wrench(one, g) + gravity_wrench(two, g)
            );
        }
    }
}

/// `measuredWrench_static`: with no motion and no gravity the measurement model reduces to the
/// frame transform alone — the new theory is a conservative extension of `TorqueWrench`, which
/// is what the static cases of the ground truth pin down.
#[test]
fn measured_wrench_static() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                for contact in wrenches() {
                    assert_eq!(
                        measured_wrench(
                            p,
                            r,
                            mp,
                            Twist::zero(),
                            Accel::zero(),
                            Vec3::zero(),
                            contact
                        ),
                        tip_to_sensor(p, r, contact)
                    );
                }
            }
        }
    }
}

/// `measuredWrench_at_rest`: a tool held at rest with no contact reads exactly the negative of
/// its gravity wrench.
///
/// One equation, and it is the sign convention of the whole model: `g` points down, gravity
/// pulls the body down with `m g`, and the sensor bears the reaction against it. Every sign in
/// the crate hangs off this test.
#[test]
fn measured_wrench_at_rest() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                for g in gravities() {
                    assert_eq!(
                        measured_wrench(
                            p,
                            r,
                            mp,
                            Twist::zero(),
                            Accel::zero(),
                            g,
                            Wrench::zero()
                        ),
                        -gravity_wrench(tip_mass_to_sensor(p, r, mp), g)
                    );
                }
            }
        }
    }
}

/// `recoveredContactWrench_measuredWrench`: **compensation is exact.** Running the measurement
/// model backwards returns the wrench that was applied, for any rotation, motion and gravity.
///
/// This is the theorem that says the gravity and inertia terms of a real controller are
/// *removable*: the frame algebra itself leaves no residual behind, and what is left in a real
/// system is the accuracy of the mass properties and the acceleration estimate, not the model.
#[test]
fn recovered_contact_wrench_measured_wrench() {
    // The full six-fold product is ~135k evaluations of both directions of the model — a
    // benchmark, not a test, in an unoptimised build. Cycling the last three lists through one
    // index keeps every datum paired with every pose and motion at a tenth of the cost.
    let (accels, gravities, wrenches) = (accels(), gravities(), wrenches());
    let mixed = accels.len().max(gravities.len()).max(wrenches.len());
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                for t in twists() {
                    for i in 0..mixed {
                        let acc = accels[i % accels.len()];
                        let g = gravities[i % gravities.len()];
                        let contact = wrenches[i % wrenches.len()];
                        let measured = measured_wrench(p, r, mp, t, acc, g, contact);
                        assert_eq!(
                            recovered_contact_wrench(p, r, mp, t, acc, g, measured),
                            contact
                        );
                    }
                }
            }
        }
    }
}

/// `recoveredContactWrench_at_rest`: a free-held tool at rest under gravity has its zero contact
/// wrench recovered exactly — the case a real force/torque sensor is tared against.
#[test]
fn recovered_contact_wrench_at_rest() {
    for p in offsets() {
        for r in rotations() {
            for mp in bodies() {
                for g in gravities() {
                    let measured = measured_wrench(
                        p,
                        r,
                        mp,
                        Twist::zero(),
                        Accel::zero(),
                        g,
                        Wrench::zero(),
                    );
                    assert_eq!(
                        recovered_contact_wrench(
                            p,
                            r,
                            mp,
                            Twist::zero(),
                            Accel::zero(),
                            g,
                            measured
                        ),
                        Wrench::zero()
                    );
                }
            }
        }
    }
}

/// `sensorAccelToTip_comp`: accelerations fold through a frame chain like everything else — the
/// two lever arms merge into `p + R q` inside the centripetal terms, which is what makes the
/// acceleration transport an honest change of frame rather than a one-step convention.
#[test]
fn sensor_accel_to_tip_comp() {
    // Pose pairs are the point of this theorem, so those stay a full product; the motion is
    // cycled through one index rather than multiplied out, for the same cost reason as
    // `recovered_contact_wrench_measured_wrench`.
    let (twists, accels) = (twists(), accels());
    for p in offsets() {
        for q in offsets() {
            for r in rotations() {
                for s in rotations() {
                    for i in 0..twists.len() {
                        let t = twists[i];
                        let acc = accels[i % accels.len()];
                        assert_eq!(
                            sensor_accel_to_tip(
                                q,
                                s,
                                sensor_twist_to_tip(p, r, t),
                                sensor_accel_to_tip(p, r, t, acc)
                            ),
                            sensor_accel_to_tip(p + r.mul_vec(q), r * s, t, acc)
                        );
                    }
                }
            }
        }
    }
}

/// `sensorMassToTip_comp`: mass descriptions fold the same way — conjugating twice is
/// conjugating by the product, and the two origin shifts compose.
#[test]
fn sensor_mass_to_tip_comp() {
    for p in offsets() {
        for q in offsets() {
            for r in rotations() {
                for s in rotations() {
                    for mp in bodies() {
                        assert_eq!(
                            sensor_mass_to_tip(q, s, sensor_mass_to_tip(p, r, mp)),
                            sensor_mass_to_tip(p + r.mul_vec(q), r * s, mp)
                        );
                    }
                }
            }
        }
    }
}
