import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.*;

import java.util.ArrayList;

/**
 * Created by lucas on 4/15/2014.
 */
public class XmodCeqZ extends PrimitiveConstraint {

    static int idNumber = 1;

    /**
     * variable x in x % c = z
     */
    public IntVar x;

    /**
     * constant c in x % c = z
     */
    public int c;

    /**
     * variable z in x % c = z
     */
    public IntVar z;

    public XmodCeqZ(IntVar x, int c, IntVar z) {

        assert (x != null) : "Variable x is null";
        assert (z != null) : "Variable z is null";

        numberId = idNumber++;
        numberArgs = 2;

        this.x = x;
        this.c = c;
        this.z = z;
    }

    @Override
    public ArrayList<Var> arguments() {

        ArrayList<Var> variables = new ArrayList<Var>(2);

        variables.add(x);
        variables.add(z);
        return variables;
    }

    @Override
    public void consistency (Store store) {

        int resultMin = IntDomain.MinInt;
        int resultMax = IntDomain.MaxInt;

        do {

            store.propagationHasOccurred = false;

//            y.domain.inComplement(store.level, y, 0);

            // Compute bounds for reminder

            int remainderMin, remainderMax;

            if (x.min() >= 0) {
                remainderMin = 0;
                remainderMax = c - 1;
            }
            else if (x.max() < 0) {
                remainderMax = 0;
                remainderMin = -c + 1;
            }
            else {
                remainderMin = Math.min(c, -c) + 1;
                remainderMax = Math.max(c, -c) - 1;
            }

            z.domain.in(store.level, z, remainderMin, remainderMax);

            // Bounds for result
            int oldResultMin = resultMin, oldResultMax = resultMax;

            IntervalDomain result = IntDomain.divBounds(x.min(), x.max(), c, c);

            resultMin = result.min();
            resultMax = result.max();

            if (oldResultMin != resultMin || oldResultMax != resultMax)
                store.propagationHasOccurred = true;

            // Bounds for Y
//            IntervalDomain yBounds = IntDomain.divBounds(x.min()-reminderMax, x.max()-reminderMin, resultMin, resultMax);
//
//            y.domain.in(store.level, y, yBounds);

            // Bounds for Z and reminder
            IntervalDomain reminder = IntDomain.mulBounds(resultMin, resultMax, c, c);
            int zMin = reminder.min(), zMax = reminder.max();

            remainderMin = x.min() - zMax;
            remainderMax = x.max() - zMin;

            z.domain.in(store.level, z, remainderMin, remainderMax);

            x.domain.in(store.level, x, zMin + z.min(), zMax + z.max());

            assert checkSolution(resultMin, resultMax) == null : checkSolution(resultMin, resultMax);

        } while (store.propagationHasOccurred);

    }

    @Override
    public void notConsistency (Store store) {

        // TODO
    }

    @Override
    public void removeConstraint() {
        z.removeConstraint(this);
        x.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {
        IntDomain Xdom = z.dom(), Zdom = x.dom();

        return Xdom.singleton() && Zdom.singleton() &&
                Zdom.min() == mod(Xdom.min(), c);
    }

    @Override
    public boolean notSatisfied() {

        return mod(x.dom().min(), c) != z.dom().min();
    }

    @Override
    public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.BOUND;
    }

    @Override
    public int getNestedPruningEvent(Var var, boolean mode) {

        // If consistency function mode
        if (mode) {
            if (consistencyPruningEvents != null) {
                Integer possibleEvent = consistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return IntDomain.BOUND;
        }

        // If notConsistency function mode
        else {
            if (notConsistencyPruningEvents != null) {
                Integer possibleEvent = notConsistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return IntDomain.GROUND;
        }

    }

    @Override
    public int getNotConsistencyPruningEvent(Var var) {

        // If notConsistency function mode
        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.GROUND;

    }

    @Override
    public void impose(Store store) {
        z.putModelConstraint(this, getConsistencyPruningEvent(z));
        x.putModelConstraint(this, getConsistencyPruningEvent(x));
        store.addChanged(this);
        store.countConstraint();
    }

    @Override
    public String toString() {
        return id() + " : XmodCeqZ(" + x + ", " + c + ", " + z + " )";
    }

    @Override
    public void increaseWeight() {
        if (increaseWeight) {
            z.weight++;
            x.weight++;
        }
    }

    String checkSolution(int resultMin, int resultMax) {
        String result = null;

        if (z.singleton() && x.singleton()) {
            result = "Operation mod does not hold " + x + " mod " + c + " = " + z + "(result "+resultMin+".."+resultMax;
            for (int i=resultMin; i<=resultMax; i++) {
                if ( i*c + z.value() == x.value() )
                    result = null;
            }
        }
        else
            result = null;
        return result;
    }

    int div(int a, int b) {
        return (int)Math.floor((float)a / (float)b);
    }

    int mod(int a, int b) {
        return a - div(a, b) * b;
    }
}
