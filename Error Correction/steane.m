
close all;
clear all;
clc;


% ------ DEFINITIONS ------

global I X Y Z H ket0 ket1 bra0 bra1 proj0 proj1 encoder stabs;

I = [1, 0; 0, 1];
X = [0, 1; 1, 0];
Y = [0, -1i; 1i, 0];
Z = [1, 0; 0, -1];
H = 1 / sqrt(2) * [1, 1; 1, -1];

ket0 = [1; 0];
ket1 = [0; 1];
bra0 = [1, 0];
bra1 = [0, 1];
proj0 = ket0 * bra0;
proj1 = ket1 * bra1;



% ------ ENCODING ------

ket0000000 = kronPow(ket0, 7);
ket1010101 = kronZeroOneList({1, 0, 1, 0, 1, 0, 1});
ket0110011 = kronZeroOneList({0, 1, 1, 0, 0, 1, 1});
ket1100110 = kronZeroOneList({1, 1, 0, 0, 1, 1, 0});
ket0001111 = kronZeroOneList({0, 0, 0, 1, 1, 1, 1});
ket1011010 = kronZeroOneList({1, 0, 1, 1, 0, 1, 0});
ket0111100 = kronZeroOneList({0, 1, 1, 1, 1, 0, 0});
ket1101001 = kronZeroOneList({1, 1, 0, 1, 0, 0, 1});

XL = kronPow(X, 7);
ZL = kronPow(Z, 7);

ket0L = 1 / sqrt(8) * (ket0000000 + ket1010101 + ket0110011 + ket1100110 + ket0001111 + ket1011010 + ket0111100 + ket1101001);
ket1L = XL * ket0L;

encoder = ket0L * bra0 + ket1L * bra1;



% ------ STABILIZERS ------

IIIXXXX = kronList({I, I, I, X, X, X, X});
IXXIIXX = kronList({I, X, X, I, I, X, X});
XIXIXIX = kronList({X, I, X, I, X, I, X});
IIIZZZZ = kronList({I, I, I, Z, Z, Z, Z});
IZZIIZZ = kronList({I, Z, Z, I, I, Z, Z});
ZIZIZIZ = kronList({Z, I, Z, I, Z, I, Z});

stabs = {IIIXXXX, IXXIIXX, XIXIXIX, IIIZZZZ, IZZIIZZ, ZIZIZIZ};




% ------ FUNCTIONS ------

function result = kronZeroOneList(list)
    global ket0 ket1;
    result = 1;
    for i = 1:length(list)
        if list{i} == 0
            result = kron(result, ket0);
        else
            result = kron(result, ket1);
        end
    end
end
% krons `phi` with itself `n` times. Example:
%   `kronPow(phi, 3)` is the same as `kron(phi, kron(phi, phi))`
function result = kronPow(phi, n)
    result = 1;
    for i = 1:n
        result = kron(result, phi);
    end
end

% krons the elements of `list` together. Example:
%   `kronList({H, I, X})` is the same as `kron(H, kron(I, X))`
function result = kronList(list)
    result = 1;
    for i = 1:length(list)
        result = kron(result, list{i});
    end
end

% Returns `true` if `A` and `B` are roughly equal up to a global phase.
% Allows for small floating point inaccuracies.
function equal = areEqualUpToGlobalPhase(A, B)
    if size(A) ~= size(B)
        equal = false;
        return;
    end
    Q = A ./ B;
    equal = max(Q) - min(Q) < 1e-20;
end

% Encodes the logical qubit `phi` using the Steane code. Returns a 7-qubit
% state.
function state = encode(phi)
    global encoder;
    state = encoder * phi;
end

% Returns 0 or 1 based on whether `state` is a +1 or -1 eigenvector of
% `stab`, respectively.
function result = getCode(state, stab)
    if stab * state == state
        result = 0;
    elseif stab * state == -state
        result = 1;
    else
        disp("INVALID!");
    end
end

% Returns a 6-length cellarray of 0s and 1s that represents the code for
% the error that has been applied to `state`.
function e = getErrorCode(state)
    global stabs;
    f = @(stab) getCode(state, stab);
    e = cellfun(f, stabs);
end

function int = threeBitsToInt(threeBits)
    int = 4 * threeBits(1) + 2 * threeBits(2) + threeBits(3);
end

% Returns a cellarray of all errors that have been applied to `state`. Each
% cell will contain a struct with the following fields:
%   - type: either "I", "X", or "Z"
%   - location: a value between 1-7
function errors = getErrorList(state)
    
    e = getErrorCode(state);
    ZLocation = threeBitsToInt(e(1:3));
    XLocation = threeBitsToInt(e(4:6));

    errors = {};

    if ZLocation > 0
        error.type = "Z";
        error.location = ZLocation;
        errors{end + 1} = error;
    end
    if XLocation > 0
        error.type = "X";
        error.location = XLocation;
        errors{end + 1} = error;
    end
end

% Corrects an error that has been applied to `state`. `error` should be a
% struct with the following fields:
%   - type: either "I", "X", or "Z"
%   - location: a value between 1-7
function result = fixError(state, error)
    
    global I X Z;
    
    switch error.type
        case "I"
            result = state;
            return;
        case "X"
            G = X;
        case "Z"
            G = Z;
    end

    correction = kronPow(I, error.location - 1);
    correction = kron(correction, G);
    correction = kron(correction, kronPow(I, 7 - error.location));

    result = correction * state;
end


% Performs `error` on the logical qubit `phi` and checks that the Steane
% code successfully recovers from it. `error` should be a 7-qubit gate.
function correct = testError(error, phi)
    
    global encoder;
    
    phiL = encode(phi);

    state = error * phiL;

    errorList = getErrorList(state);
    for i = 1:length(errorList)
        state = fixError(state, errorList{i});
    end

    correct = areEqualUpToGlobalPhase(state, phiL);
end
% Performs `error` on all 7 locations and checks that the Steane code can
% recover each time. `error` should be a single-qubit gate, and `phi`
% should be a single qubit.
function correct = testAllErrorLocations(error, phi)
    global I;
    correct = true;
    for loc = 1:7
        fullError = kron(kronPow(I, loc - 1), kron(error, kronPow(I, 7 - loc)));
        correct = correct && testError(fullError, phi);
    end
end
% Performs all possible errors (all 4 types and all 7 locations) on `phi`
% and checks that the Steane code can recover from each one.
function correct = testAllErrors(phi)

    global I X Z;

    % Test I
    correct = testError(kronPow(I, 7), phi);

    % Test X and Z
    for error = {X, Z, X * Z, Z * X}
        correct = correct && testAllErrorLocations(error{1}, phi);
    end
end

% Returns a random unitary qubit.
function phi = randomQubit()
    alpha = randn() + randn() * 1i;
    beta = randn() + randn() * 1i;
    phi = [alpha; beta];
    phi = phi / norm(phi);
end

% Tests all possible errors on `n` random qubits.
function testAllErrorsOnRandomQubits(n)
    failureCount = 0;
    for i = 1:n
        % Display status indicators
        if mod(i, n / 100) == 0
            fprintf("%d%%\n", i / (n / 100));
        end
        result = testAllErrors(randomQubit());
        if ~result
            failureCount = failureCount + 1;
        end
    end
    fprintf("Completed %d tests with %d errors.\n", n, failureCount);
end

testAllErrorsOnRandomQubits(1000);
