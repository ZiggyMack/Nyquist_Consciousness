
import React, { useState } from 'react';
import Header from './components/Header';
import PxlSimulator from './components/PxlSimulator';
import Chat from './components/Chat';
import Live from './components/Live';

type Tab = 'simulator' | 'chat' | 'live';

const App: React.FC = () => {
  const [activeTab, setActiveTab] = useState<Tab>('simulator');
  const [agentIdentity, setAgentIdentity] = useState<string | null>(null);

  const renderContent = () => {
    switch (activeTab) {
      case 'simulator':
        return <PxlSimulator agentIdentity={agentIdentity} setAgentIdentity={setAgentIdentity} />;
      case 'chat':
        return <Chat />;
      case 'live':
        return <Live agentIdentity={agentIdentity} />;
      default:
        return <PxlSimulator agentIdentity={agentIdentity} setAgentIdentity={setAgentIdentity} />;
    }
  };

  return (
    <div className="min-h-screen bg-slate-900 text-slate-300 antialiased">
      <Header activeTab={activeTab} setActiveTab={setActiveTab} agentIdentity={agentIdentity} />
      <main className="container mx-auto p-4 md:p-8">
        {renderContent()}
        <footer className="text-center mt-12 text-slate-500 text-sm">
          <p>Powered by Protopraxic Logic. All rights reserved.</p>
        </footer>
      </main>
    </div>
  );
};

export default App;
